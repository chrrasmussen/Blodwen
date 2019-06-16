module Compiler.Erlang.Common

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

%default covering

genString : String -> String
genString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c =
      if isAlphaNum c || c == '_'
        then cast c
        else "C" ++ show (cast {to=Int} c) ++ "_"

mutual
  genName : Name -> String
  genName (UN n) = "un_" ++ genString n
  genName (MN n i) = genString n ++ "_" ++ show i
  genName (NS ns n) = "ns_" ++ showSep "_" ns ++ "_" ++ genName n
  genName (HN n i) = "hn_" ++ genString n ++ "__" ++ show i
  genName (PV n d) = "pat__" ++ genName n
  genName (DN _ n) = "dn_" ++ genName n
  genName (GN g) = "gn_" ++ genGName g

  genGName : GenName -> String
  genGName (Nested o i) = "nested__" ++ genName i ++ "__in__" ++ genName o
  genGName (CaseBlock n i) = "case__" ++ genName n ++ "_" ++ show i
  genGName (WithBlock n i) = "with__" ++ genName n ++ "_" ++ show i

-- local variable names as scheme names - we need to invent new names for the locals
-- because there might be shadows in the original expression which can't be resolved
-- by the same scoping rules. (e.g. something that computes \x, x => x + x where the
-- names are the same but refer to different bindings in the scope)
public export
data SVars : List Name -> Type where
  Nil : SVars []
  (::) : (svar : String) -> SVars ns -> SVars (n :: ns)

extendSVars : (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
extendSVars {ns} xs vs = extSVars' (cast (length ns)) xs vs
  where
    extSVars' : Int -> (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
    extSVars' i [] vs = vs
    extSVars' i (x :: xs) vs = genName (MN "V" i) :: extSVars' (i + 1) xs vs

initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []

lookupSVar : Elem x xs -> SVars xs -> String
lookupSVar Here (n :: ns) = n
lookupSVar (There p) (n :: ns) = lookupSVar p ns

export
genConstructor : Int -> List String -> String
genConstructor t args = "{" ++ showSep ", " (show t :: args) ++ "}"

op : String -> List String -> String
op o args = o ++ "(" ++ showSep ", " args ++ ")"

infixop : String -> String -> String -> String
infixop o x y = "(" ++ x ++ " " ++ o ++ " " ++ y ++ ")"

boolToInt : String -> String
boolToInt condition = "case " ++ condition ++ " of false -> 0; _ -> 1 end"

genOp : PrimFn arity -> Vect arity String -> String
genOp (Add IntType) [x, y] = op "int_add" [x, y, "63"]
genOp (Sub IntType) [x, y] = op "int_sub" [x, y, "63"]
genOp (Mul IntType) [x, y] = op "int_mult" [x, y, "63"]
genOp (Div IntType) [x, y] = op "int_div" [x, y, "63"]
genOp (Add ty) [x, y] = infixop "+" x y
genOp (Sub ty) [x, y] = infixop "-" x y
genOp (Mul ty) [x, y] = infixop "*" x y
genOp (Div IntegerType) [x, y] = infixop "div" x y -- NOTE: Is allowed to be partial
genOp (Div ty) [x, y] = infixop "/" x y -- NOTE: Is allowed to be partial
genOp (Mod ty) [x, y] = infixop "rem" x y -- NOTE: Is allowed to be partial -- TODO: Can `x` and `y` be floating point? `rem` does not work on floating points
genOp (Neg ty) [x] = op "-" [x]
genOp (LT StringType) [x, y] = op "unicode_string_lt" [x, y]
genOp (LTE StringType) [x, y] = op "unicode_string_lte" [x, y]
genOp (EQ StringType) [x, y] = op "unicode_string_eq" [x, y]
genOp (GTE StringType) [x, y] = op "unicode_string_gte" [x, y]
genOp (GT StringType) [x, y] = op "unicode_string_gt" [x, y]
genOp (LT ty) [x, y] = boolToInt (infixop "<" x y)
genOp (LTE ty) [x, y] = boolToInt (infixop "=<" x y)
genOp (EQ ty) [x, y] = boolToInt (infixop "=:=" x y)
genOp (GTE ty) [x, y] = boolToInt (infixop ">=" x y)
genOp (GT ty) [x, y] = boolToInt (infixop ">" x y)
genOp StrLength [x] = op "unicode_string_length" [x]
genOp StrHead [x] = op "unicode_string_head" [x]
genOp StrTail [x] = op "unicode_string_tail" [x]
genOp StrIndex [x, i] = op "unicode_string_index" [x, i]
genOp StrCons [x, y] = op "unicode_string_cons" [x, y]
genOp StrAppend [x, y] = op "unicode_string_append" [x, y]
genOp StrReverse [x] = op "unicode_string_reverse" [x]
genOp StrSubstr [x, y, z] = op "unicode_string_substr" [x, y, z]

genOp (Cast IntType StringType) [x] = op "blodwen_int_to_string" [x]
genOp (Cast IntegerType StringType) [x] = op "blodwen_integer_to_string" [x]
genOp (Cast DoubleType StringType) [x] = op "blodwen_double_to_string" [x]
genOp (Cast CharType StringType) [x] = op "blodwen_char_to_string" [x]

genOp (Cast IntType IntegerType) [x] = op "blodwen_int_to_integer" [x]
genOp (Cast DoubleType IntegerType) [x] = op "blodwen_double_to_integer" [x]
genOp (Cast CharType IntegerType) [x] = op "blodwen_char_to_integer" [x]
genOp (Cast StringType IntegerType) [x] = op "blodwen_string_to_integer" [x]

genOp (Cast IntegerType IntType) [x] = op "blodwen_integer_to_int" [x]
genOp (Cast DoubleType IntType) [x] = op "blodwen_double_to_int" [x]
genOp (Cast CharType IntType) [x] = op "blodwen_char_to_int" [x]
genOp (Cast StringType IntType) [x] = op "blodwen_string_to_int" [x]

genOp (Cast IntType DoubleType) [x] = op "blodwen_int_to_double" [x]
genOp (Cast IntegerType DoubleType) [x] = op "blodwen_integer_to_double" [x]
genOp (Cast StringType DoubleType) [x] = op "blodwen_string_to_double" [x]

genOp (Cast IntType CharType) [x] = op "blodwen_int_to_char" [x]

genOp (Cast from to) [x] = "throw(\"Invalid cast " ++ show from ++ "->" ++ show to ++ "\")"

genOp BelieveMe [_, _, x] = x

public export
data ExtPrim
  = CCall | PutStr | GetStr
  | FileOpen | FileClose | FileReadLine | FileWriteLine | FileEOF
  | NewIORef | ReadIORef | WriteIORef
  | ErlUnsafeCall | ErlCall | ErlCase | ErlReceive
  | InternalTryCatch
  | Unknown Name

export
Show ExtPrim where
  show CCall = "CCall"
  show PutStr = "PutStr"
  show GetStr = "GetStr"
  show FileOpen = "FileOpen"
  show FileClose = "FileClose"
  show FileReadLine = "FileReadLine"
  show FileWriteLine = "FileWriteLine"
  show FileEOF = "FileEOF"
  show NewIORef = "NewIORef"
  show ReadIORef = "ReadIORef"
  show WriteIORef = "WriteIORef"
  show ErlUnsafeCall = "ErlUnsafeCall"
  show ErlCall = "ErlCall"
  show ErlCase = "ErlCase"
  show ErlReceive = "ErlReceive"
  show InternalTryCatch = "InternalTryCatch"
  show (Unknown n) = "Unknown " ++ show n

toPrim : Name -> ExtPrim
toPrim pn@(NS _ n) = cond [
  (n == UN "prim__cCall", CCall),
  (n == UN "prim__putStr", PutStr),
  (n == UN "prim__getStr", GetStr),
  (n == UN "prim__open", FileOpen),
  (n == UN "prim__close", FileClose),
  (n == UN "prim__readLine", FileReadLine),
  (n == UN "prim__writeLine", FileWriteLine),
  (n == UN "prim__eof", FileEOF),
  (n == UN "prim__newIORef", NewIORef),
  (n == UN "prim__readIORef", ReadIORef),
  (n == UN "prim__writeIORef", WriteIORef),
  (n == UN "prim__erlUnsafeCall", ErlUnsafeCall),
  (n == UN "prim__erlCall", ErlCall),
  (n == UN "prim__erlCase", ErlCase),
  (n == UN "prim__erlReceive", ErlReceive),
  (n == UN "internal__tryCatch", InternalTryCatch)
  ]
  (Unknown pn)
toPrim pn = Unknown pn


mkBlodwenRtsAtom : String
mkBlodwenRtsAtom = "'$blodwen_rts'"

mkErased : String
mkErased = "erased"

mkUnit : String
mkUnit = "{}"

-- PrimIO.MkIORes : {0 a : Type} -> a -> (1 x : %World) -> IORes a
export
mkWorld : String -> String
mkWorld res = genConstructor 0 [mkErased, res, "false"]

-- io_pure : {0 a : Type} -> a -> IO a
-- io_pure {a} x = MkIO {a} (\1 w : %World => (MkIORes {a} x w))
--
-- ns_PrimIO_un_io_pure(V_0, V_1) -> {0, erased, fun(V_2) -> {0, erased, V_1, V_2} end}.
mkIOPure : String -> String
mkIOPure val = "{0, " ++ mkErased ++ ", fun(World) -> {0, " ++ mkErased ++ ", " ++ val ++ ", World} end}"


mkCurriedFun : List String -> String -> String
mkCurriedFun []        body = body
mkCurriedFun (x :: xs) body = "fun(" ++ x ++ ") -> " ++ mkCurriedFun xs body ++ " end"

mkUncurriedFun : List String -> String -> String
mkUncurriedFun xs body = "fun(" ++ showSep ", " xs ++ ") -> " ++ body ++ " end"

mkStringToAtom : String -> String
mkStringToAtom str = "(binary_to_atom(unicode:characters_to_binary(" ++ str ++ "), utf8))"

mkTryCatch : String -> String
mkTryCatch str = "(fun() -> try " ++ str ++ " of Result -> Result catch Class:Reason:Stacktrace -> {" ++ mkBlodwenRtsAtom ++ ", {Class, Reason, Stacktrace}} end end())"

-- TODO: Not a great workaround :-/
-- Will fail if the input string is not a string literal
stripErlangString : String -> String
stripErlangString str =
  pack (reverse (drop 8 (reverse (drop 3 (unpack str)))))

genConstant : Constant -> String
genConstant (I x) = show x
genConstant (BI x) = show x
genConstant (Str x) = "<<" ++ show x ++ "/utf8>>"
genConstant (Ch x) = show $ cast {to=Int} x
genConstant (Db x) = show x
genConstant WorldVal = "false" -- TODO: What is the point of `false` here, and `true` for the rest of the cases?
genConstant IntType = "true"
genConstant IntegerType = "true"
genConstant StringType = "true"
genConstant CharType = "true"
genConstant DoubleType = "true"
genConstant WorldType = "true"

genCaseDef : Maybe String -> List String
genCaseDef Nothing = []
genCaseDef (Just tm) = ["(_) -> " ++ tm]


applyUnsafePerformIO : CExp vars -> CExp vars
applyUnsafePerformIO expr = CApp (CRef (NS ["PrimIO"] (UN "unsafePerformIO"))) [CErased, expr]

applyToArgs : CExp vars -> List (CExp vars) -> CExp vars
applyToArgs expr [] = expr
applyToArgs expr (x :: xs) = applyToArgs (CApp expr [x]) xs

expectArgAtIndex : (n : Nat) -> List a -> Core annot a
expectArgAtIndex n xs =
  case index' n xs of
    Just val => pure val
    Nothing => throw (InternalError ("Missing expected argument at index " ++ show n ++ " in list"))


unitCExp : CExp vars
unitCExp =
  CCon (NS ["Builtin"] (UN "MkUnit")) 0 []

ioPureCExp : CExp vars -> CExp vars
ioPureCExp expr =
  CCon (NS ["PrimIO"] (UN "MkIO")) 0 [CErased, CLam (MN "World" 0) (CCon (NS ["PrimIO"] (UN "MkIORes")) 0 [CErased, weaken expr, CLocal Here])]

tryCatchCExp : CExp vars -> CExp vars
tryCatchCExp expr =
  CExtPrim (NS [] (UN "internal__tryCatch")) [expr]

curryCExp : List Name -> ({innerVars : List Name} -> CExp innerVars -> CExp innerVars) -> CExp vars -> CExp vars
curryCExp allNames transformer expr = wrapLambda allNames (transformer (CApp (weakenNs allNames expr) (reverse (args allNames))))
  where
    wrapLambda : (names : List Name) -> CExp (names ++ vars) -> CExp vars
    wrapLambda []        innerExpr = innerExpr
    wrapLambda (x :: xs) innerExpr = wrapLambda xs (CLam x innerExpr)

    args : (names : List Name) -> List (CExp (names ++ vars))
    args [] = []
    args (x :: xs) = CLocal Here :: map weaken (args xs)


mutual
  bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> List String
  bindArgs i [] vs = []
  bindArgs i (n :: ns) (v :: vs) = v :: bindArgs (i + 1) ns vs

  genConAltTuple : Int -> SVars vars -> (args : List Name) -> CExp (args ++ vars) -> (arity : Nat) -> Core annot String
  genConAltTuple i vs args sc arity = do
    let vs' = extendSVars args vs
    pure $ "({" ++ showSep ", " (drop arity $ bindArgs 1 args vs') ++ "}) -> " ++ !(genExp i vs' sc)

  -- Given an Erlang function `ErlangFunc` with arity 2:
  -- 1. Curries this function according to arity: fun(X_0) -> fun(X_1) -> ErlangFunc(X_0, X_1) end end
  -- 2. Transform the inner result with a user-defined function: fun(X_0) -> fun(X_1) -> `Transformer`(ErlangFunc(X_0, X_1)) end end
  -- The transformer is specifically used to lift the value into the IO monad
  genConAltFun : Int -> SVars vars -> (args : List Name) -> CExp (args ++ vars) -> (arity : Nat) -> (String -> String) -> Core annot String
  genConAltFun i vs args sc arity transformer = do
    let vs' = extendSVars args vs
    let tempVars = take arity $ zipWith (\name, idx => name ++ show idx) (repeat "X_") [0..]
    pure  $ "(Func) -> " ++ mkUncurriedFun (drop (S arity) $ bindArgs 1 args vs') !(genExp i vs' sc) ++ "(" ++ mkCurriedFun tempVars (transformer ("Func(" ++ showSep ", " tempVars ++ ")")) ++ ")"

  genConAlt : Int -> SVars vars -> CConAlt vars -> Core annot String
  -- Unit
  genConAlt i vs (MkConAlt (NS ["Builtin"] (UN "MkUnit")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "(" ++ mkUnit ++ ") -> " ++ !(genExp i vs' sc)
  -- Bool
  genConAlt i vs (MkConAlt (NS ["Prelude"] (UN "True")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "(true) -> " ++ !(genExp i vs' sc)
  genConAlt i vs (MkConAlt (NS ["Prelude"] (UN "False")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "(false) -> " ++ !(genExp i vs' sc)
  -- List
  genConAlt i vs (MkConAlt (NS ["Prelude"] (UN "Nil")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "([]) -> " ++ !(genExp i vs' sc)
  genConAlt i vs (MkConAlt (NS ["Prelude"] (UN "::")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "([" ++ showSep " | " (drop 1 $ bindArgs 1 args vs') ++ "]) -> " ++ !(genExp i vs' sc)
  -- Raw
  genConAlt i vs (MkConAlt (NS ["Idris", "ErlangPrelude"] (UN "MkRaw")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "(" ++ !(expectArgAtIndex 1 (bindArgs 1 args vs')) ++ ") -> " ++ !(genExp i vs' sc)
  -- ErlAtom
  genConAlt i vs (MkConAlt (NS ["Atoms", "ErlangPrelude"] (UN "MkErlAtom")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "(Atom) -> fun(" ++ !(expectArgAtIndex 0 (bindArgs 1 args vs')) ++ ") -> " ++ !(genExp i vs' sc) ++ " end(atom_to_binary(Atom, utf8))"
  -- ErlBinary
  genConAlt i vs (MkConAlt (NS ["Strings", "ErlangPrelude"] (UN "MkErlBinary")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "(" ++ !(expectArgAtIndex 0 (bindArgs 1 args vs')) ++ ") -> " ++ !(genExp i vs' sc)
  -- ErlAtom
  genConAlt i vs (MkConAlt (NS ["Strings", "ErlangPrelude"] (UN "MkErlCharlist")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "(" ++ !(expectArgAtIndex 0 (bindArgs 1 args vs')) ++ ") -> " ++ !(genExp i vs' sc)
  -- ErlNil
  genConAlt i vs (MkConAlt (NS ["Lists", "ErlangPrelude"] (UN "Nil")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "([]) -> " ++ !(genExp i vs' sc)
  -- ErlCons
  genConAlt i vs (MkConAlt (NS ["Lists", "ErlangPrelude"] (UN "::")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "([" ++ showSep " | " (drop 2 $ bindArgs 1 args vs') ++ "]) -> " ++ !(genExp i vs' sc)
  -- ErlList
  genConAlt i vs (MkConAlt (NS ["ProperLists", "ErlangPrelude"] (UN "Nil")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "([]) -> " ++ !(genExp i vs' sc)
  genConAlt i vs (MkConAlt (NS ["ProperLists", "ErlangPrelude"] (UN "::")) tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "([" ++ showSep " | " (drop 2 $ bindArgs 1 args vs') ++ "]) -> " ++ !(genExp i vs' sc)
  -- ErlTuple/A
  genConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple0")) tag args sc) = genConAltTuple i vs args sc 0
  genConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple1")) tag args sc) = genConAltTuple i vs args sc 1
  genConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple2")) tag args sc) = genConAltTuple i vs args sc 2
  genConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple3")) tag args sc) = genConAltTuple i vs args sc 3
  genConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple4")) tag args sc) = genConAltTuple i vs args sc 4
  genConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple5")) tag args sc) = genConAltTuple i vs args sc 5
  -- ErlFun/A
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun0")) tag args sc) = genConAltFun i vs args sc 0 id
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun1")) tag args sc) = genConAltFun i vs args sc 1 id
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun2")) tag args sc) = genConAltFun i vs args sc 2 id
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun3")) tag args sc) = genConAltFun i vs args sc 3 id
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun4")) tag args sc) = genConAltFun i vs args sc 4 id
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun5")) tag args sc) = genConAltFun i vs args sc 5 id
  -- ErlIO/A
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO0")) tag args sc) = genConAltFun i vs args sc 0 mkIOPure
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO1")) tag args sc) = genConAltFun i vs args sc 1 mkIOPure
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO2")) tag args sc) = genConAltFun i vs args sc 2 mkIOPure
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO3")) tag args sc) = genConAltFun i vs args sc 3 mkIOPure
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO4")) tag args sc) = genConAltFun i vs args sc 4 mkIOPure
  genConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO5")) tag args sc) = genConAltFun i vs args sc 5 mkIOPure
  -- Other
  genConAlt i vs (MkConAlt n tag args sc) = do
    let vs' = extendSVars args vs
    pure $ "({" ++ showSep ", " (show tag :: bindArgs 1 args vs') ++ "}) -> " ++ !(genExp i vs' sc)

  genConstAlt : Int -> SVars vars -> CConstAlt vars -> Core annot String
  genConstAlt i vs (MkConstAlt c exp) = pure $ "(" ++ genConstant c ++ ") -> " ++ !(genExp i vs exp)

  genConTuple : Int -> SVars vars -> List (CExp vars) -> Core annot String
  genConTuple i vs args = pure $ "{" ++ showSep ", " !(traverse (genExp i vs) args) ++ "}"

  -- Given an Idris function `idrisFun` with arity 2:
  -- 1. Uncurries this function according to arity: fun(X_0, X_1) -> (idrisFun(X_0))(X_1) end
  -- 2. Transform the inner result with a user-defined function: fun(X_0, X_1) -> `transform`((idrisFun(X_0))(X_1)) end
  -- The transformer is specifically used to perform the side-effects of the result (using `unsafePerformIO`)
  genConFun : Int -> SVars vars -> (arity : Nat) -> CExp vars -> (CExp vars -> CExp vars) -> Core annot String
  genConFun i vs arity func transformer = do
    let tempVars = take arity $ zipWith (\name, idx => name ++ show idx) (repeat "X_") [0..]
    let tempCRefs = take arity $ zipWith (\name, idx => CRef (MN name idx)) (repeat "X") [0..]
    let body = transformer (applyToArgs func tempCRefs)
    pure $ mkUncurriedFun tempVars !(genExp i vs body)

  genCon : Int -> SVars vars -> CExp vars -> Core annot String
  -- Unit
  genCon i vs (CCon (NS ["Builtin"] (UN "MkUnit")) _ _) = pure mkUnit
  -- Bool
  genCon i vs (CCon (NS ["Prelude"] (UN "True")) _ _) = pure "true"
  genCon i vs (CCon (NS ["Prelude"] (UN "False")) _ _) = pure "false"
  -- List
  genCon i vs (CCon (NS ["Prelude"] (UN "Nil")) _ _) = pure "[]"
  genCon i vs (CCon (NS ["Prelude"] (UN "::")) _ [_, x, xs]) = pure $ "[" ++ !(genExp i vs x) ++ " | " ++ !(genExp i vs xs) ++ "]"
  -- Raw
  genCon i vs (CCon (NS ["Idris", "ErlangPrelude"] (UN "MkRaw")) _ [_, x]) = pure $ !(genExp i vs x)
  -- ErlAtom
  genCon i vs (CCon (NS ["Atoms", "ErlangPrelude"] (UN "MkErlAtom")) _ [x]) = pure $ mkStringToAtom !(genExp i vs x)
  -- ErlBinary
  genCon i vs (CCon (NS ["Strings", "ErlangPrelude"] (UN "MkErlBinary")) _ [x]) = pure $ "unicode:characters_to_binary(" ++ !(genExp i vs x) ++ ")"
  -- ErlCharlist
  genCon i vs (CCon (NS ["Strings", "ErlangPrelude"] (UN "MkErlCharlist")) _ [x]) = pure $ "unicode:characters_to_list(" ++ !(genExp i vs x) ++ ")"
  -- ErlNil
  genCon i vs (CCon (NS ["Lists", "ErlangPrelude"] (UN "Nil")) _ []) = pure "[]"
  -- ErlCons
  genCon i vs (CCon (NS ["Lists", "ErlangPrelude"] (UN "::")) _ [_, _, x, y]) = pure $ "[" ++ !(genExp i vs x) ++ " | " ++ !(genExp i vs y) ++ "]"
  -- ErlList
  genCon i vs (CCon (NS ["ProperLists", "ErlangPrelude"] (UN "Nil")) _ []) = pure "[]"
  genCon i vs (CCon (NS ["ProperLists", "ErlangPrelude"] (UN "::")) _ [_, _, x, xs]) = pure $ "[" ++ !(genExp i vs x) ++ " | " ++ !(genExp i vs xs) ++ "]"
  -- ErlTuple/A
  genCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple0")) _ []) = genConTuple i vs []
  genCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple1")) _ args) = genConTuple i vs (drop 1 args)
  genCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple2")) _ args) = genConTuple i vs (drop 2 args)
  genCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple3")) _ args) = genConTuple i vs (drop 3 args)
  genCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple4")) _ args) = genConTuple i vs (drop 4 args)
  genCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple5")) _ args) = genConTuple i vs (drop 5 args)
  -- ErlFun/A
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun0")) _ args) = genConFun i vs 0 !(expectArgAtIndex 1 args) id
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun1")) _ args) = genConFun i vs 1 !(expectArgAtIndex 2 args) id
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun2")) _ args) = genConFun i vs 2 !(expectArgAtIndex 3 args) id
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun3")) _ args) = genConFun i vs 3 !(expectArgAtIndex 4 args) id
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun4")) _ args) = genConFun i vs 4 !(expectArgAtIndex 5 args) id
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun5")) _ args) = genConFun i vs 5 !(expectArgAtIndex 6 args) id
  -- ErlIO/A
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO0")) _ args) = genConFun i vs 0 !(expectArgAtIndex 1 args) applyUnsafePerformIO
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO1")) _ args) = genConFun i vs 1 !(expectArgAtIndex 2 args) applyUnsafePerformIO
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO2")) _ args) = genConFun i vs 2 !(expectArgAtIndex 3 args) applyUnsafePerformIO
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO3")) _ args) = genConFun i vs 3 !(expectArgAtIndex 4 args) applyUnsafePerformIO
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO4")) _ args) = genConFun i vs 4 !(expectArgAtIndex 5 args) applyUnsafePerformIO
  genCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO5")) _ args) = genConFun i vs 5 !(expectArgAtIndex 6 args) applyUnsafePerformIO
  -- Other
  genCon i vs (CCon x tag args) = pure $ genConstructor tag !(traverse (genExp i vs) args)
  genCon i vs tm = throw (InternalError ("Invalid constructor: " ++ show tm))

  -- oops, no traverse for Vect in Core
  genArgs : Int -> SVars vars -> Vect n (CExp vars) -> Core annot (Vect n String)
  genArgs i vs [] = pure []
  genArgs i vs (arg :: args) = pure $ !(genExp i vs arg) :: !(genArgs i vs args)

  export
  genExp : Int -> SVars vars -> CExp vars -> Core annot String
  genExp i vs (CLocal el) = pure $ lookupSVar el vs
  genExp i vs (CRef n) = pure $ genName n
  genExp i vs (CLam x sc) = do
    let vs' = extendSVars [x] vs
    sc' <- genExp i vs' sc
    pure $ "fun(" ++ lookupSVar Here vs' ++ ") -> " ++ sc' ++ " end"
  genExp i vs (CLet x val sc) = do
    let vs' = extendSVars [x] vs
    val' <- genExp i vs val
    sc' <- genExp i vs' sc
    pure $ "(fun(" ++ lookupSVar Here vs' ++ ") -> " ++ sc' ++ " end(" ++ val' ++ "))"
  genExp i vs (CApp x args) =
    pure $ "(" ++ !(genExp i vs x) ++ "(" ++ showSep ", " !(traverse (genExp i vs) args) ++ "))"
  genExp i vs con@(CCon x tag args) =
    genCon i vs con
  genExp i vs (COp op args) =
    pure $ genOp op !(genArgs i vs args)
  genExp i vs (CExtPrim p args) =
    genExtPrim i vs (toPrim p) args
  genExp i vs (CForce t) =
    pure $ "(" ++ !(genExp i vs t) ++ "())" -- TODO: Should use another mechanism to avoid evaluating delayed computation multiple times
  genExp i vs (CDelay t) =
    pure $ "fun() -> " ++ !(genExp i vs t) ++ " end"
  genExp i vs (CConCase sc alts def) = do
    tcode <- genExp i vs sc
    defc <- maybe (pure Nothing) (\v => pure (Just !(genExp i vs v))) def
    conAlts <- traverse (genConAlt i vs) alts
    pure $ "(fun " ++
      showSep "; " (conAlts ++ genCaseDef defc) ++
      " end(" ++ tcode ++ "))"
  genExp i vs (CConstCase sc alts def) = do
    defc <- maybe (pure Nothing) (\v => pure (Just !(genExp i vs v))) def
    tcode <- genExp i vs sc
    constAlts <- traverse (genConstAlt i vs) alts
    let isMatchingOnString = case head' alts of
      Just (MkConstAlt (Str _) _) => True
      _ => False
    let matchOnValue = if isMatchingOnString
      then "unicode:characters_to_binary(" ++ tcode ++ ", utf8)"
      else tcode
    pure $ "(fun " ++
      showSep "; " (constAlts ++ genCaseDef defc) ++
      " end(" ++ matchOnValue ++ "))"
  genExp i vs (CPrimVal c) =
    pure $ genConstant c
  genExp i vs CErased =
    pure mkErased
  genExp i vs (CCrash msg) =
    pure $ "throw(\"" ++ msg ++ "\")"

  -- Evaluate the outer `ErlList` to figure out the arity of the function call
  readArgs : Int -> SVars vars -> CExp vars -> Core annot (List String)
  readArgs i vs (CCon (NS ["ProperLists", "ErlangPrelude"] (UN "Nil")) _ []) = pure []
  readArgs i vs (CCon (NS ["ProperLists", "ErlangPrelude"] (UN "::")) _ [_, _, x, xs]) = pure $ !(genExp i vs x) :: !(readArgs i vs xs)
  readArgs i vs tm = throw (InternalError ("Unknown argument to foreign call: " ++ show tm))

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  genExtPrim : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  genExtPrim i vs CCall [ret, fn, args, world] =
    throw (InternalError ("Can't compile C FFI calls to Erlang yet"))
  genExtPrim i vs PutStr [arg, world] =
    pure $ "(fun() -> io_unicode_put_str(" ++ !(genExp i vs arg) ++ "), " ++ mkWorld mkUnit ++ " end())"
  genExtPrim i vs GetStr [world] =
    pure $ mkWorld "io_unicode_get_str(\"\")"
  genExtPrim i vs FileOpen [file, mode, bin, world] =
    pure $ mkWorld $ "blodwen_open(" ++ !(genExp i vs file) ++ ", " ++ !(genExp i vs mode) ++ ", " ++ !(genExp i vs bin) ++ ")"
  genExtPrim i vs FileClose [file, world] =
    pure $ "(fun() -> blodwen_close(" ++ !(genExp i vs file) ++ "), " ++ mkWorld mkUnit ++ " end())"
  genExtPrim i vs FileReadLine [file, world] =
    pure $ mkWorld $ "blodwen_read_line(" ++ !(genExp i vs file) ++ ")"
  genExtPrim i vs FileWriteLine [file, str, world] =
    pure $ mkWorld $ "blodwen_write_line(" ++ !(genExp i vs file) ++ ", " ++ !(genExp i vs str) ++ ")"
  genExtPrim i vs FileEOF [file, world] =
    pure $ mkWorld $ "blodwen_eof(" ++ !(genExp i vs file) ++ ")"
  genExtPrim i vs NewIORef [_, val, world] =
    pure $ mkWorld $ "(box " ++ !(genExp i vs val) ++ ")"
  genExtPrim i vs ReadIORef [_, ref, world] =
    pure $ mkWorld $ "(unbox " ++ !(genExp i vs ref) ++ ")"
  genExtPrim i vs WriteIORef [_, ref, val, world] =
    pure $ mkWorld $ "(set-box! " ++ !(genExp i vs ref) ++ " " ++ !(genExp i vs val) ++ ")"
  genExtPrim i vs ErlUnsafeCall [_, ret, CPrimVal (Str fn), args, world] = do
    parameterList <- readArgs i vs args
    pure $ mkWorld $ "(" ++ fn ++ "(" ++ showSep ", " parameterList ++ "))"
  genExtPrim i vs ErlUnsafeCall [_, ret, fn, args, world] =
    pure $ mkWorld "false" -- TODO: Implement?
  genExtPrim i vs ErlCall [_, modName, fnName, args@(CCon _ _ _), world] = do
    parameterList <- readArgs i vs args
    pure $ mkWorld $ mkTryCatch $ "(" ++ mkStringToAtom !(genExp i vs modName) ++ ":" ++ mkStringToAtom !(genExp i vs fnName) ++ "(" ++ showSep ", " parameterList ++ "))"
  genExtPrim i vs ErlCall [_, modName, fnName, args, world] =
    pure $ mkWorld "false" -- TODO: Implement?
  genExtPrim i vs ErlCase [_, def, matchers@(CCon _ _ _), term] = do
    clauses <- readMatchers i 0 vs matchers
    genErlCase i vs def clauses term
  genExtPrim i vs ErlCase [_, def, matchers, tm] =
    pure $ mkWorld "false" -- TODO: Do I need to implement this to make `erlCase` work with variables?
  genExtPrim i vs ErlReceive [_, timeout, def, matchers@(CCon _ _ _), world] = do
    clauses <- readMatchers i 0 vs matchers
    genErlReceive i vs timeout def clauses
  genExtPrim i vs ErlReceive [_, timeout, def, matchers, world] =
    pure $ mkWorld "false" -- TODO: Do I need to implement this to make `erlReceive` work with variables?
  genExtPrim i vs InternalTryCatch [expr] =
    pure $ mkTryCatch !(genExp i vs expr)
  genExtPrim i vs (Unknown n) args =
    throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  genExtPrim i vs prim args =
    throw (InternalError ("Badly formed external primitive " ++ show prim ++ " " ++ show args))

  data GuardBinOp = LTE | LT | EQ | GT | GTE

  data ErlGuard : List Name -> Type where
    IsAny     : ErlGuard vars
    IsInteger : CExp vars -> ErlGuard vars
    IsDouble  : CExp vars -> ErlGuard vars
    IsBinary  : CExp vars -> ErlGuard vars
    IsList    : CExp vars -> ErlGuard vars
    IsAtom    : CExp vars -> ErlGuard vars
    IsMap     : CExp vars -> ErlGuard vars
    IsPid     : CExp vars -> ErlGuard vars
    IsRef     : CExp vars -> ErlGuard vars
    IsPort    : CExp vars -> ErlGuard vars
    IsFun     : Nat -> CExp vars -> ErlGuard vars
    IsBinOp   : GuardBinOp -> CExp vars -> CExp vars -> ErlGuard vars
    AndAlso   : ErlGuard vars -> ErlGuard vars -> ErlGuard vars
    OrElse    : ErlGuard vars -> ErlGuard vars -> ErlGuard vars

  record ErlClause (vars : List Name) where
    constructor MkErlClause
    nextLocal : Int
    globals : List (CExp vars)
    pattern : String
    guard : ErlGuard vars
    body : CExp vars

  concatGlobals : List (ErlClause vars) -> List (CExp vars)
  concatGlobals clauses = clauses >>= globals

  concatGuards : List (ErlClause vars) -> ErlGuard vars
  concatGuards clauses = foldl AndAlso IsAny (map guard clauses)

  nextGlobal : (global : Int) -> List (ErlClause vars) -> Int
  nextGlobal global clauses = global + cast (length (concatGlobals clauses))

  readMatchers : Int -> (global : Int) -> SVars vars -> CExp vars -> Core annot (List (ErlClause vars))
  readMatchers i global vs (CCon (NS ["Prelude"] (UN "Nil")) _ _) = pure []
  readMatchers i global vs (CCon (NS ["Prelude"] (UN "::")) _ [_, x, xs]) = do
    first <- readClause i 0 global vs x
    rest <- readMatchers i (nextGlobal global [first]) vs xs
    pure (first :: rest)
  readMatchers i global vs args =
    throw (InternalError ("Expected a list of matchers " ++ show args))

  readListLength : Int -> SVars vars -> CExp vars -> Core annot Nat
  readListLength i vs (CCon (NS ["Prelude"] (UN "Nil")) _ _) = pure 0
  readListLength i vs (CCon (NS ["Prelude"] (UN "::")) _ [_, x, xs]) = do
    tailLength <- readListLength i vs xs
    pure (1 + tailLength)
  readListLength i vs args =
    throw (InternalError ("Expected a list of types " ++ show args))

  createGuardClause : Int -> (local : Int) -> (global : Int) -> SVars vars -> (createGuard : CExp vars -> ErlGuard vars) -> Core annot (ErlClause vars)
  createGuardClause i local global vs createGuard = do
    let ref = CRef (MN "C" local)
    pure $ MkErlClause (local + 1) [] !(genExp i vs ref) (createGuard ref) ref

  readClause : Int -> (local : Int) -> (global : Int) -> SVars vars -> CExp vars -> Core annot (ErlClause vars)
  -- MExact
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MExact")) _ [_, _, matchValue]) = do
    let localRef = CRef (MN "C" global)
    let globalRef = CRef (MN "G" global)
    pure $ MkErlClause (local + 1) [matchValue] !(genExp i vs localRef) (IsBinOp EQ localRef globalRef) unitCExp
  -- MAny
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MAny")) _ []) = do
    let ref = CRef (MN "C" local)
    pure $ MkErlClause (local + 1) [] !(genExp i vs ref) IsAny ref
  -- Simple guards
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MCodepoint")) _ []) = createGuardClause i local global vs
    (\val => AndAlso (IsInteger val) (AndAlso (IsBinOp GTE val (CPrimVal (BI 0))) (IsBinOp LTE val (CPrimVal (BI 0x10FFFF)))))
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MInteger")) _ []) = createGuardClause i local global vs IsInteger
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MDouble")) _ []) = createGuardClause i local global vs IsDouble
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MAtom")) _ []) = createGuardClause i local global vs IsAtom
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MBinary")) _ []) = createGuardClause i local global vs IsBinary
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MMap")) _ []) = createGuardClause i local global vs IsMap
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MPid")) _ []) = createGuardClause i local global vs IsPid
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MRef")) _ []) = createGuardClause i local global vs IsRef
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MPort")) _ []) = createGuardClause i local global vs IsPort
  -- MNil
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MNil")) _ []) =
    pure $ MkErlClause local [] "[]" IsAny unitCExp
  -- MCons
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MCons")) _ [_, _, _, headMatcher, tailMatcher, mapper]) = do
    headClause <- readClause i local global vs headMatcher
    tailClause <- readClause i (nextLocal headClause) (nextGlobal global [headClause]) vs tailMatcher
    pure $ MkErlClause (nextLocal tailClause) (concatGlobals [headClause, tailClause])
      ("[" ++ pattern headClause ++ " | " ++ pattern tailClause ++ "]")
      (concatGuards [headClause, tailClause])
      (CApp (CApp mapper [body headClause]) [body tailClause])
  -- MList
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MList")) _ [_, _, xs, mapper]) = do
    clauses <- readClauseErlMatchers i local global vs xs mapper
    let nextLoc = maybe local nextLocal (last' clauses)
    pure $ MkErlClause nextLoc (concatGlobals clauses)
      ("[" ++ showSep ", " (map pattern clauses) ++ "]")
      (concatGuards clauses)
      (applyToArgs mapper (map body clauses))
  -- MTuple
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MTuple")) _ [_, _, xs, mapper]) = do
    clauses <- readClauseErlMatchers i local global vs xs mapper
    let nextLoc = maybe local nextLocal (last' clauses)
    pure $ MkErlClause nextLoc (concatGlobals clauses)
      ("{" ++ showSep ", " (map pattern clauses) ++ "}")
      (concatGuards clauses)
      (applyToArgs mapper (map body clauses))
  -- MMapSubset
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MMapSubset")) _ [_, _, xs, mapper]) = do
    clauses <- readClauseErlMatchers i local global vs xs mapper
    let nextLoc = maybe local nextLocal (last' clauses)
    pure $ MkErlClause nextLoc (concatGlobals clauses)
      ("#{" ++ showSep ", " (map pattern clauses) ++ "}")
      (concatGuards clauses)
      (applyToArgs mapper (map body clauses))
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MkErlMapEntry")) _ [_, _, _, key, valueMatcher]) = do
    let globalRef = CRef (MN "G" global)
    clause <- readClause i local (global + 1) vs valueMatcher
    pure $ MkErlClause (nextLocal clause) (key :: globals clause) (!(genExp i vs globalRef) ++ " := " ++ (pattern clause)) (guard clause) (body clause)
  -- MIO
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MIO")) _ [types]) = do
    let ref = CRef (MN "C" local)
    arity <- readListLength i vs types
    let tempVars = take arity $ zipWith (\name, idx => MN name idx) (repeat "M") [0..]
    pure $ MkErlClause local [] !(genExp i vs ref) (IsFun arity ref) (curryCExp tempVars (ioPureCExp . tryCatchCExp) ref)
  -- MError
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MError")) _ [_, matcher]) = do
    clause <- readClause i local global vs matcher
    pure $ MkErlClause (nextLocal clause) (globals clause) ("{" ++ mkBlodwenRtsAtom ++ ", " ++ pattern clause ++ "}") (guard clause) (body clause)
  -- MMapper
  readClause i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "MMapper")) _ [_, _, matcher, mapper]) = do
    clause <- readClause i local global vs matcher
    pure $ MkErlClause (nextLocal clause) (globals clause) (pattern clause) (guard clause) (CApp mapper [body clause])
  -- Other
  readClause i local global vs matcher =
    throw (InternalError ("Badly formed clause " ++ show matcher))

  readClauseErlMatchers : Int -> (local : Int) -> (global : Int) -> SVars vars -> CExp vars -> (mapper : CExp vars) -> Core annot (List (ErlClause vars))
  readClauseErlMatchers i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "Nil")) _ _) mapper = pure []
  readClauseErlMatchers i local global vs (CCon (NS ["CaseExpr", "ErlangPrelude"] (UN "::")) _ [_, _, _, x, xs]) mapper = do
    first <- readClause i local global vs x
    rest <- readClauseErlMatchers i (nextLocal first) (nextGlobal global [first]) vs xs mapper
    pure (first :: rest)
  readClauseErlMatchers i local global vs args mapper =
    throw (InternalError ("Badly formed ErlMatchers " ++ show args))

  genGuard : Int -> SVars vars -> ErlGuard vars -> Core annot String
  genGuard i vs IsAny = pure "true"
  genGuard i vs (IsInteger ref) = pure $ "is_integer(" ++ !(genExp i vs ref) ++ ")"
  genGuard i vs (IsDouble ref) = pure $ "is_float(" ++ !(genExp i vs ref) ++ ")"
  genGuard i vs (IsBinary ref) = pure $ "is_binary(" ++ !(genExp i vs ref) ++ ")"
  genGuard i vs (IsList ref) = pure $ "is_list(" ++ !(genExp i vs ref) ++ ")"
  genGuard i vs (IsAtom ref) = pure $ "is_atom(" ++ !(genExp i vs ref) ++ ")"
  genGuard i vs (IsMap ref) = pure $ "is_map(" ++ !(genExp i vs ref) ++ ")"
  genGuard i vs (IsPid ref) = pure $ "is_pid(" ++ !(genExp i vs ref) ++ ")"
  genGuard i vs (IsRef ref) = pure $ "is_reference(" ++ !(genExp i vs ref) ++ ")"
  genGuard i vs (IsPort ref) = pure $ "is_port(" ++ !(genExp i vs ref) ++ ")"
  genGuard i vs (IsFun arity ref) = pure $ "is_function(" ++ !(genExp i vs ref) ++ ", " ++ show arity ++ ")"
  genGuard i vs (IsBinOp LTE ref1 ref2) = pure $ !(genExp i vs ref1) ++ " =< " ++ !(genExp i vs ref2)
  genGuard i vs (IsBinOp LT ref1 ref2) = pure $ !(genExp i vs ref1) ++ " < " ++ !(genExp i vs ref2)
  genGuard i vs (IsBinOp EQ ref1 ref2) = pure $ !(genExp i vs ref1) ++ " =:= " ++ !(genExp i vs ref2)
  genGuard i vs (IsBinOp GT ref1 ref2) = pure $ !(genExp i vs ref1) ++ " > " ++ !(genExp i vs ref2)
  genGuard i vs (IsBinOp GTE ref1 ref2) = pure $ !(genExp i vs ref1) ++ " >= " ++ !(genExp i vs ref2)
  genGuard i vs (AndAlso g1 g2) = pure $ "(" ++ !(genGuard i vs g1) ++ " andalso " ++ !(genGuard i vs g2) ++ ")"
  genGuard i vs (OrElse g1 g2) = pure $ "(" ++ !(genGuard i vs g1) ++ " orelse " ++ !(genGuard i vs g2) ++ ")"

  genClause : Int -> SVars vars -> ErlClause vars -> Core annot String
  genClause i vs (MkErlClause _ _ pattern guard body) =
    pure $ "(" ++ pattern ++ ") when " ++ !(genGuard i vs guard) ++ " -> " ++ !(genExp i vs body)

  genErlCase : Int -> SVars vars -> (def : CExp vars) -> List (ErlClause vars) -> (term : CExp vars) -> Core annot String
  genErlCase i vs def clauses term = do
    globalValues <- traverse (genExp i vs) (concatGlobals clauses)
    let globalVars = take (length globalValues) $ (zipWith (\name, idx => name ++ show idx) (repeat "G_") [0..])
    clausesStr <- traverse (genClause i vs) clauses
    defStr <- pure $ "(_) -> " ++ !(genExp i vs def)
    pure $ "(fun(" ++ showSep ", " globalVars ++") -> " ++
      "(fun " ++
      showSep "; " (clausesStr ++ [defStr]) ++
      " end(" ++ !(genExp i vs term) ++ "))" ++
      " end(" ++ showSep ", " globalValues ++ "))"

  genErlReceive : Int -> SVars vars -> (timeout : CExp vars) -> (def : CExp vars) -> List (ErlClause vars) -> Core annot String
  genErlReceive i vs timeout def clauses = do
    globalValues <- traverse (genExp i vs) (concatGlobals clauses)
    let globalVars = take (length globalValues) $ (zipWith (\name, idx => name ++ show idx) (repeat "G_") [0..])
    clausesStr <- traverse (genClause i vs) clauses
    pure $ mkWorld $ "(fun(" ++ showSep ", " globalVars ++") -> " ++
      "(receive " ++
      showSep "; " clausesStr ++
      " after " ++ !(genExp i vs timeout) ++ " -> " ++ !(genExp i vs def) ++ " end)" ++
      " end(" ++ showSep ", " globalValues ++ "))"

genArglist : SVars ns -> String
genArglist [] = ""
genArglist [x] = x
genArglist (x :: xs) = x ++ ", " ++ genArglist xs

genDef : Name -> CDef -> Core annot String
genDef n (MkFun args exp) = do
  let vs = initSVars args
  pure $ genName n ++ "(" ++ genArglist vs ++ ") -> " ++ !(genExp 0 vs exp) ++ ".\n"
genDef n (MkError exp) =
  pure $ genName n ++ "() -> " ++ !(genExp 0 [] exp) ++ ".\n"
genDef n (MkCon t a) =
  pure "" -- Nothing to compile here

data InternalArity = Value | Arity Nat

internalArity : CExp vars -> InternalArity
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETFun")) _ _) = Arity 1
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlFun0")) _ _) = Arity 0
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlFun1")) _ _) = Arity 1
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlFun2")) _ _) = Arity 2
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlFun3")) _ _) = Arity 3
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlFun4")) _ _) = Arity 4
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlFun5")) _ _) = Arity 5
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlIO0")) _ _) = Arity 0
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlIO1")) _ _) = Arity 1
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlIO2")) _ _) = Arity 2
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlIO3")) _ _) = Arity 3
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlIO4")) _ _) = Arity 4
internalArity (CCon (NS ["ErlangPrelude"] (UN "ETErlIO5")) _ _) = Arity 5
internalArity _ = Value

externalArity : InternalArity -> Nat
externalArity Value = 0
externalArity (Arity arity) = arity

genExports : Int -> SVars vars -> CExp vars -> Core annot (List (String, Nat, String))
genExports i vs (CCon (NS ["IO", "ErlangPrelude"] (UN "Fun")) _ [_, exprTy, name, expr]) = do
  let intArity = internalArity exprTy
  let extArity = externalArity intArity
  let funcName = stripErlangString !(genExp i vs name)
  let vars = take extArity $ zipWith (\name, idx => name ++ show idx) (repeat "E_") [0..]
  let invocation =
    case intArity of
      Value => ""
      Arity => "(" ++ showSep ", " vars ++ ")"
  let funcDecl = funcName ++ "(" ++ showSep ", " vars ++ ") -> " ++ !(genExp i vs expr) ++ invocation ++ "."
  pure $ [(funcName, extArity, funcDecl)]
genExports i vs (CCon (NS ["IO", "ErlangPrelude"] (UN "Combine")) _ [exports1, exports2]) =
  pure $ !(genExports i vs exports1) ++ !(genExports i vs exports2)
genExports i vs tm = throw (InternalError ("Invalid export: " ++ show tm))

getCompileExpr : Defs -> Name -> Core annot CDef
getCompileExpr defs name = do
  let Just globalDef = lookupGlobalExact name (gamma defs)
    | throw (InternalError ("Compiling undefined name " ++ show name))
  let Just expr = compexpr globalDef
    | throw (InternalError ("No compiled definition for " ++ show name))
  pure expr

-- Convert the name to Erlang code
-- (There may be no code generated, for example if it's a constructor)
export
genErlang : Defs -> Name -> Core annot String
genErlang defs name = do
  expr <- getCompileExpr defs name
  genDef name expr

export
genErlangExports : Defs -> Name -> Core annot (String, String)
genErlangExports defs name = do
  MkFun args expr <- getCompileExpr defs name
    | throw (InternalError ("Expected function definition for " ++ show name)) 
  let vs = initSVars args
  exports <- genExports 0 vs expr
  let exportDirectives = "-export([" ++ showSep ", " (map (\(name, arity, _) => name ++ "/" ++ show arity) exports) ++ "]).\n"
  let exportFuncs = showSep "\n" (map (\(_, _, funcDef) => funcDef) exports)
  pure (exportDirectives, exportFuncs)
