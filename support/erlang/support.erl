% -module(main).
% -export([main/1]).
-compile([nowarn_unused_function, nowarn_unused_vars]).


% Debugging

debug_inspect(Val) ->
  io:format("~p~n", [Val]),
  Val.


% General

% NOTE: This function assume that any lists are IO lists
% If this assumption changes in the future, one possible solution
% is to wrap IO lists in a tuple, e.g. `{str, IoList}`
blodwen_normalize_value(X) when is_list(X) -> list_to_binary(X);
blodwen_normalize_value(X) -> X.



% NOTE: This function will try to evaluate the some value into proper Erlang value.
% At the moment it only supports evaluating list arguments.
blodwen_eval_arg({0, {}}) -> [];
blodwen_eval_arg({1, {}, Hd, Tl}) -> [Hd | blodwen_eval_arg(Tl)];
blodwen_eval_arg(X) -> X.


% Unit

-define(UNIT, {0}).

-type idr_unit() :: ?UNIT.


% Booleans

-define(TRUE, 1).
-define(FALSE, 0).

-type idr_bool() :: ?TRUE | ?FALSE.

% TODO: Not in use by code generator
-spec blodwen_bool_to_int(boolean()) -> idr_bool().
blodwen_bool_to_int(false) -> ?FALSE;
blodwen_bool_to_int(_) -> ?TRUE.


% Either

-type idr_either(Left, Right) :: {0, false, false, Left} | {1, false, false, Right}.

-spec either_left(any()) -> idr_either(any(), any()).
either_left(X) -> {0, false, false, X}.

-spec either_right(any()) -> idr_either(any(), any()).
either_right(X) -> {1, false, false, X}.


% Arithmetic

-spec int_pow(integer(), integer()) -> integer().
int_pow(N, M) -> int_pow(N, M, 1).

-spec int_pow(integer(), integer(), integer()) -> integer().
int_pow(_, 0, R) -> R;
int_pow(N, M, R) -> int_pow(N, M - 1, R * N).

int_add(X, Y, Bits) -> (X + Y) rem int_pow(2, Bits).
int_sub(X, Y, Bits) -> (X - Y) rem int_pow(2, Bits).
int_mult(X, Y, Bits) -> (X * Y) rem int_pow(2, Bits).
int_div(X, Y, Bits) -> (X div Y) rem int_pow(2, Bits).


% Comparisons

unicode_string_lt(X, Y) -> blodwen_bool_to_int(iolist_to_binary(X) < iolist_to_binary(Y)).
unicode_string_lte(X, Y) -> blodwen_bool_to_int(iolist_to_binary(X) =< iolist_to_binary(Y)).
unicode_string_eq(X, Y) -> blodwen_bool_to_int(iolist_to_binary(X) == iolist_to_binary(Y)).
unicode_string_gte(X, Y) -> blodwen_bool_to_int(iolist_to_binary(X) >= iolist_to_binary(Y)).
unicode_string_gt(X, Y) -> blodwen_bool_to_int(iolist_to_binary(X) > iolist_to_binary(Y)).


% Strings

% -type idr_char() :: integer(). % TODO: Use for anything?


% NOTE: Must be total
unicode_string_length(Str) -> string:length(Str).

% NOTE: Is allowed to be partial
unicode_string_head(Str) ->
  [Hd | _] = string:next_grapheme(Str),
  Hd.

% NOTE: Is allowed to be partial
unicode_string_tail(Str) ->
  [_ | Tl] = string:next_grapheme(Str),
  Tl.

% NOTE: Is allowed to be partial
unicode_string_index(Str, Index) ->
  CharStr = string:slice(Str, Index, 1),
  [Hd | _] = string:next_grapheme(CharStr),
  Hd.


% NOTE: Must be total
unicode_string_cons(Char, Str) -> [Char | Str].

% NOTE: Must be total
unicode_string_append(Str1, Str2) -> [Str1 | Str2].

% NOTE: Must be total
unicode_string_reverse(Str) -> string:reverse(Str).

% NOTE: Must be total
unicode_string_substr(Start, Len, Str) -> string:substr(Str, Start, Len).


% Casts

blodwen_int_to_string(Int) -> integer_to_binary(Int).
blodwen_integer_to_string(Integer) -> integer_to_binary(Integer).
blodwen_double_to_string(Double) -> float_to_binary(Double).
blodwen_char_to_string(Char) -> [Char].

blodwen_int_to_integer(Int) -> Int.
blodwen_double_to_integer(Double) -> floor(Double). % NOTE: Solved similar to Chez
blodwen_char_to_integer(Char) -> Char. % NOTE: Char is already an integer
blodwen_string_to_integer(Str) -> binary_to_integer(iolist_to_binary(Str)). % TODO: Will crash if string contains other characters than digits. Do I need to consider special prefixes like `0x`, `0b`, `0` or similar?

blodwen_integer_to_int(Integer) -> Integer.
blodwen_double_to_int(Double) -> floor(Double).
blodwen_char_to_int(Char) -> Char. % NOTE: Char is already an integer
blodwen_string_to_int(Str) -> binary_to_integer(iolist_to_binary(Str)). % TODO: Will crash if string contains other characters than digits. Do I need to consider special prefixes like `0x`, `0b`, `0` or similar?

blodwen_int_to_double(Int) -> float(Int).
blodwen_integer_to_double(Integer) -> float(Integer).
blodwen_string_to_double(Str) -> binary_to_float(iolist_to_binary(Str)). % TODO: Will crash if string contains other characters than digits. Must also include a dot to be a valid double number.

blodwen_int_to_char(Char) -> Char. % NOTE: Char is an integer


% IO

io_unicode_put_str(Str) ->
  io:format("~ts", [Str]).

io_unicode_get_str(Prompt) ->
  Line = io:get_line(Prompt),
  string:trim(Line, trailing, "\n").


% Files

-type handle() :: file:io_device() | undefined.
-type error_code() :: integer().

% TODO: Return error number instead (in all cases)?
-spec blodwen_open(binary(), binary(), idr_bool()) -> idr_either(error_code(), handle()).
blodwen_open(File, Mode, Bin) ->
  Flags = case Mode of
    <<"r">> -> [read];
    <<"w">> -> [write];
    _ -> throw("I haven't worked that one out yet, sorry...")
  end,
  {ok, Pid} = file:open(File, Flags),
  either_right(Pid).

% TODO: Return error number instead?
-spec blodwen_close(handle()) -> idr_unit().
blodwen_close(Pid) ->
  case file:close(Pid) of
    ok -> ?UNIT;
    _ -> throw("I haven't worked that one out yet, sorry...")
  end.

% TODO: Return error number instead?
-spec blodwen_read_line(handle()) -> idr_either(error_code(), binary()).
blodwen_read_line(Pid) ->
  case file:read_line(Pid) of
    {ok, Line} -> either_right(Line);
    eof -> either_right(<<>>);
    _ -> throw("I haven't worked that one out yet, sorry...")
  end.

-spec blodwen_write_line(handle(), binary()) -> idr_either(error_code(), idr_unit()).
blodwen_write_line(Pid, Bytes) ->
  case file:write(Pid, Bytes) of
    ok -> either_right(?TRUE);
    _ -> either_right(?FALSE)
  end.

% COPIED FROM: https://github.com/lenary/idris-erlang/blob/master/irts/idris_erlang_rts.erl
-spec blodwen_eof(handle()) -> idr_bool().
blodwen_eof(undefined) ->
  ?TRUE; % Null is at EOF
blodwen_eof(Handle) ->
  case file:read(Handle, 1) of
    eof -> ?TRUE; % At EOF
    {ok, _} ->
      case file:position(Handle, {cur, -1}) of
        {ok, _} -> ?FALSE; % Not at EOF
        {error, _} -> ?TRUE % Error Scanning Back => EOF
      end;
    {error, _} -> ?TRUE % Error => EOF
  end.
