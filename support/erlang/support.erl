% Unit

-define(UNIT, {}).

-type idr_unit() :: ?UNIT.


% Booleans

-define(TRUE, 1).
-define(FALSE, 0).

-type idr_bool() :: ?TRUE | ?FALSE.

-spec blodwen_bool_to_int(boolean()) -> idr_bool().
blodwen_bool_to_int(false) -> ?FALSE;
blodwen_bool_to_int(_) -> ?TRUE.


% Either
% TODO: Hard-coded data constructor
% Must match the behavior of `Compiler.Erlang.Common.genConstructor` and `Compiler.Erlang.Common.genName`

-type idr_either(Left, Right) :: {ns_Prelude_un_Left, erased, erased, Left} | {ns_Prelude_un_Right, erased, erased, Right}.

-spec either_left(any()) -> idr_either(any(), any()).
either_left(X) -> {ns_Prelude_un_Left, erased, erased, X}.

-spec either_right(any()) -> idr_either(any(), any()).
either_right(X) -> {ns_Prelude_un_Right, erased, erased, X}.


% List

-type idr_list(A) :: {0, {}} | {1, {}, A, idr_list(A)}.

-spec list_to_idr_list(list(any())) -> idr_list(any()).
list_to_idr_list([]) -> {0, {}};
list_to_idr_list([Hd | Tl]) -> {1, {}, Hd, list_to_idr_list(Tl)}.


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

unicode_string_lt(X, Y) -> blodwen_bool_to_int(unicode:characters_to_binary(X) < unicode:characters_to_binary(Y)).
unicode_string_lte(X, Y) -> blodwen_bool_to_int(unicode:characters_to_binary(X) =< unicode:characters_to_binary(Y)).
unicode_string_eq(X, Y) -> blodwen_bool_to_int(unicode:characters_to_binary(X) =:= unicode:characters_to_binary(Y)).
unicode_string_gte(X, Y) -> blodwen_bool_to_int(unicode:characters_to_binary(X) >= unicode:characters_to_binary(Y)).
unicode_string_gt(X, Y) -> blodwen_bool_to_int(unicode:characters_to_binary(X) > unicode:characters_to_binary(Y)).


% Strings

% -type idr_char() :: integer() | [integer()]. % TODO: Use for anything?


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

blodwen_integer_to_int(Integer) -> Integer.
blodwen_integer_to_double(Integer) -> float(Integer).
blodwen_integer_to_string(Integer) -> integer_to_binary(Integer).

blodwen_int_to_integer(Int) -> Int.
blodwen_int_to_double(Int) -> float(Int).
blodwen_int_to_char(Char) -> Char. % NOTE: Char is an integer
blodwen_int_to_string(Int) -> integer_to_binary(Int).

blodwen_double_to_integer(Double) -> trunc(Double).
blodwen_double_to_int(Double) -> trunc(Double).
blodwen_double_to_string(Double) -> float_to_binary(Double, [{decimals, 10}, compact]).

blodwen_char_to_integer(Char) when is_integer(Char) -> Char;
blodwen_char_to_integer(_) -> 0. % NOTE: Cast will fail on unicode characters that require more than 1 codepoint.
blodwen_char_to_int(Char) -> blodwen_char_to_integer(Char).
blodwen_char_to_string(Char) -> [Char].

blodwen_string_to_integer(Str) ->
  case string:to_integer(Str) of
    {error, no_integer} ->
      0;
    {Num, StrRest} ->
      case string:next_grapheme(StrRest) of
        [] -> Num;
        _ -> 0
      end
  end.
blodwen_string_to_int(Str) -> blodwen_string_to_integer(Str). % TODO: Should `Int` be capped at a certain precision?
blodwen_string_to_double(Str) ->
  case string:to_float(Str) of
    {error, no_float} ->
      Integer = blodwen_string_to_integer(Str),
      float(Integer);
    {Num, StrRest} ->
      case string:next_grapheme(StrRest) of
        [] -> Num;
        _ -> 0.0
      end
  end.


% IO

io_unicode_put_str(Str) ->
  io:format("~ts", [Str]).

io_unicode_get_str(Prompt) ->
  Line = io:get_line(Prompt),
  string:trim(Line, trailing, "\n").


% Files

% Relevant docs: http://erlang.org/doc/man/file.html

-type handle() :: file:io_device() | undefined.

% TODO: Support more error codes
-define(ERROR_CODE_UNKNOWN, -1).
-type error_code() :: ?ERROR_CODE_UNKNOWN.


-spec mode_flags(iolist()) -> [file:mode()].
mode_flags(Mode) ->
  ModesFlags = case unicode:characters_to_binary(Mode) of
    <<"r">> -> [read];
    <<"w">> -> [write];
    <<"a">> -> [append];
    <<"r+">> -> [read, write];
    _ -> []
  end.

-spec bin_flags(idr_bool()) -> [file:mode()].
bin_flags(Bin) ->
  case Bin of
    ?TRUE -> [binary];
    _ -> []
  end.

-spec blodwen_open(file:name_all(), iolist(), idr_bool()) -> idr_either(error_code(), handle()).
blodwen_open(File, Mode, Bin) ->
  Flags = mode_flags(Mode) ++ bin_flags(Bin),
  case file:open(File, Flags) of
    {ok, Pid} -> either_right(Pid);
    _ -> either_left(?ERROR_CODE_UNKNOWN)
  end.

-spec blodwen_close(handle()) -> idr_unit().
blodwen_close(Pid) ->
  file:close(Pid),
  ?UNIT.

-spec blodwen_read_line(handle()) -> idr_either(error_code(), binary()).
blodwen_read_line(Pid) ->
  case file:read_line(Pid) of
    {ok, Line} -> either_right(Line);
    eof -> either_right(<<>>);
    _ -> either_left(?ERROR_CODE_UNKNOWN)
  end.

-spec blodwen_write_line(handle(), binary()) -> idr_either(error_code(), idr_unit()).
blodwen_write_line(Pid, Bytes) ->
  case file:write(Pid, Bytes) of
    ok -> either_right(?UNIT);
    _ -> either_left(?ERROR_CODE_UNKNOWN)
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
