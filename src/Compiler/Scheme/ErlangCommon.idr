module Compiler.Scheme.ErlangCommon

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

%default covering

schString : String -> String
schString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c == '_'
                  then cast c
                  else "C" ++ show (cast {to=Int} c) ++ "_"

mutual
  schName : Name -> String
  schName (UN n) = "un_" ++ schString n
  schName (MN n i) = schString n ++ "_" ++ show i
  schName (NS ns n) = "ns_" ++ showSep "_" ns ++ "_" ++ schName n
  schName (HN n i) = "hn_" ++ schString n ++ "__" ++ show i
  schName (PV n d) = "pat__" ++ schName n
  schName (DN _ n) = "dn_" ++ schName n
  schName (GN g) = "gn_" ++ schGName g

  schGName : GenName -> String
  schGName (Nested o i) = "nested__" ++ schName i ++ "__in__" ++ schName o
  schGName (CaseBlock n i) = "case__" ++ schName n ++ "_" ++ show i
  schGName (WithBlock n i) = "with__" ++ schName n ++ "_" ++ show i

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
    extSVars' i (x :: xs) vs = schName (MN "V" i) :: extSVars' (i + 1) xs vs

initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []

lookupSVar : Elem x xs -> SVars xs -> String
lookupSVar Here (n :: ns) = n
lookupSVar (There p) (n :: ns) = lookupSVar p ns

export
schConstructor : Int -> List String -> String
schConstructor t args = "{" ++ showSep ", " (show t :: args) ++ "}"

op : String -> List String -> String
op o args = o ++ "(" ++ showSep ", " args ++ ")"

infixop : String -> String -> String -> String
infixop o x y = "(" ++ x ++ " " ++ o ++ " " ++ y ++ ")"

boolToInt : String -> String
boolToInt condition = "case " ++ condition ++ " of false -> 0; _ -> 1 end"

schOp : PrimFn arity -> Vect arity String -> String
schOp (Add IntType) [x, y] = op "int_add" [x, y, "63"]
schOp (Sub IntType) [x, y] = op "int_sub" [x, y, "63"]
schOp (Mul IntType) [x, y] = op "int_mult" [x, y, "63"]
schOp (Div IntType) [x, y] = op "int_div" [x, y, "63"]
schOp (Add ty) [x, y] = infixop "+" x y
schOp (Sub ty) [x, y] = infixop "-" x y
schOp (Mul ty) [x, y] = infixop "*" x y
schOp (Div IntegerType) [x, y] = infixop "div" x y -- TODO: Is allowed to be partial
schOp (Div ty) [x, y] = infixop "/" x y -- TODO: Is allowed to be partial
schOp (Mod ty) [x, y] = infixop "rem" x y -- TODO: Is allowed to be partial. Can `x` and `y` be floating point? `rem` does not work on floating points
schOp (Neg ty) [x] = op "-" [x]
schOp (LT StringType) [x, y] = op "unicode_string_lt" [x, y]
schOp (LTE StringType) [x, y] = op "unicode_string_lte" [x, y]
schOp (EQ StringType) [x, y] = op "unicode_string_eq" [x, y]
schOp (GTE StringType) [x, y] = op "unicode_string_gte" [x, y]
schOp (GT StringType) [x, y] = op "unicode_string_gt" [x, y]
schOp (LT ty) [x, y] = boolToInt (infixop "<" x y)
schOp (LTE ty) [x, y] = boolToInt (infixop "=<" x y)
schOp (EQ ty) [x, y] = boolToInt (infixop "==" x y)
schOp (GTE ty) [x, y] = boolToInt (infixop ">=" x y)
schOp (GT ty) [x, y] = boolToInt (infixop ">" x y)
schOp StrLength [x] = op "unicode_string_length" [x]
schOp StrHead [x] = op "unicode_string_head" [x]
schOp StrTail [x] = op "unicode_string_tail" [x]
schOp StrIndex [x, i] = op "unicode_string_index" [x, i]
schOp StrCons [x, y] = op "unicode_string_cons" [x, y]
schOp StrAppend [x, y] = op "unicode_string_append" [x, y]
schOp StrReverse [x] = op "unicode_string_reverse" [x]
schOp StrSubstr [x, y, z] = op "unicode_string_substr" [x, y, z]

schOp (Cast IntType StringType) [x] = op "blodwen_int_to_string" [x]
schOp (Cast IntegerType StringType) [x] = op "blodwen_integer_to_string" [x]
schOp (Cast DoubleType StringType) [x] = op "blodwen_double_to_string" [x]
schOp (Cast CharType StringType) [x] = op "blodwen_char_to_string" [x]

schOp (Cast IntType IntegerType) [x] = op "blodwen_int_to_integer" [x]
schOp (Cast DoubleType IntegerType) [x] = op "blodwen_double_to_integer" [x]
schOp (Cast CharType IntegerType) [x] = op "blodwen_char_to_integer" [x]
schOp (Cast StringType IntegerType) [x] = op "blodwen_string_to_integer" [x]

schOp (Cast IntegerType IntType) [x] = op "blodwen_integer_to_int" [x]
schOp (Cast DoubleType IntType) [x] = op "blodwen_double_to_int" [x]
schOp (Cast CharType IntType) [x] = op "blodwen_char_to_int" [x]
schOp (Cast StringType IntType) [x] = op "blodwen_string_to_int" [x]

schOp (Cast IntType DoubleType) [x] = op "blodwen_int_to_double" [x]
schOp (Cast IntegerType DoubleType) [x] = op "blodwen_integer_to_double" [x]
schOp (Cast StringType DoubleType) [x] = op "blodwen_string_to_double" [x]

schOp (Cast IntType CharType) [x] = op "blodwen_int_to_char" [x]

schOp (Cast from to) [x] = "throw(\"Invalid cast " ++ show from ++ "->" ++ show to ++ "\")"

public export
data ExtPrim = CCall | ErlangCall | PutStr | GetStr
             | FileOpen | FileClose | FileReadLine | FileWriteLine | FileEOF
             | NewIORef | ReadIORef | WriteIORef
             | Unknown Name

export
Show ExtPrim where
  show CCall = "CCall"
  show ErlangCall = "ErlangCall"
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
  show (Unknown n) = "Unknown " ++ show n

toPrim : Name -> ExtPrim
toPrim pn@(NS _ n) 
    = cond [(n == UN "prim__erlangCall", ErlangCall),
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
            (n == UN "prim__writeIORef", WriteIORef)
            ]
           (Unknown pn)
toPrim pn = Unknown pn


mkUnit : String
mkUnit = "{}"

export
mkWorld : String -> String
mkWorld res = schConstructor 0 ["false", res, "false"] -- PrimIO.MkIORes : {0 a : Type} -> a -> (1 x : %World) -> IORes a -- TODO: Is the `false`s necessary?

-- io_pure : {0 a : Type} -> a -> IO a
-- io_pure {a} x = MkIO {a} (\1 w : %World => (MkIORes {a} x w))
--
-- ns_PrimIO_un_io_pure(V_0, V_1) -> {0, {}, fun(V_2) -> {0, {}, V_1, V_2} end}.
mkIOPure : String -> String
mkIOPure val = "{0, {}, fun(World) -> {0, {}, " ++ val ++ ", World} end}"


mkCurriedFun : List String -> String -> String
mkCurriedFun []        body = body
mkCurriedFun (x :: xs) body = "fun(" ++ x ++ ") -> " ++ mkCurriedFun xs body ++ " end"

mkUncurriedFun : List String -> String -> String
mkUncurriedFun xs body = "fun(" ++ showSep ", " xs ++ ") -> " ++ body ++ " end"


schConstant : Constant -> String
schConstant (I x) = show x
schConstant (BI x) = show x
schConstant (Str x) = "<<" ++ show x ++ "/utf8>>"
schConstant (Ch x) = show $ cast {to=Int} x
schConstant (Db x) = show x
schConstant WorldVal = "false" -- TODO: What is the point of `false` here, and `true` for the rest of the cases?
schConstant IntType = "true"
schConstant IntegerType = "true"
schConstant StringType = "true"
schConstant CharType = "true"
schConstant DoubleType = "true"
schConstant WorldType = "true"

schCaseDef : Maybe String -> List String
schCaseDef Nothing = []
schCaseDef (Just tm) = ["(_) -> " ++ tm]


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


parameters (schExtPrim : {vars : _} -> Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String)
  mutual
    bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> List String
    bindArgs i [] vs = []
    bindArgs i (n :: ns) (v :: vs) = v :: bindArgs (i + 1) ns vs

    schConAltTuple : (arity : Nat) -> Int -> SVars vars -> (args : List Name) -> CExp (args ++ vars) -> Core annot String
    schConAltTuple arity i vs args sc = do
      let vs' = extendSVars args vs
      pure $ "({" ++ showSep ", " (drop arity $ bindArgs 1 args vs') ++ "}) -> " ++ !(schExp i vs' sc)

    -- Given an Erlang function `ErlangFunc` with arity 2:
    -- 1. Curries this function according to arity: fun(X_1) -> fun(X_2) -> ErlangFunc(X_1, X_2) end end
    -- 2. Transform the inner result with a user-defined function: fun(X_1) -> fun(X_2) -> `Transformer`(ErlangFunc(X_1, X_2)) end end
    -- The transformer is specifically used to lift the value into the IO monad
    schConAltFun : Int -> SVars vars -> (args : List Name) -> CExp (args ++ vars) -> (arity : Nat) -> (String -> String) -> Core annot String
    schConAltFun i vs args sc arity transformer = do
      let vs' = extendSVars args vs
      let tempVars = take arity $ zipWith (\name, idx => name ++ show idx) (repeat "X_") [1..]
      pure  $ "(Func) -> " ++ mkUncurriedFun (drop (S arity) $ bindArgs 1 args vs') !(schExp i vs' sc) ++ "(" ++ mkCurriedFun tempVars (transformer ("Func(" ++ showSep ", " tempVars ++ ")")) ++ ")"

    schConAlt : Int -> SVars vars -> CConAlt vars -> Core annot String
    schConAlt i vs (MkConAlt (NS ["Builtin"] (UN "MkUnit")) tag args sc) = do
      let vs' = extendSVars args vs
      pure $ "(" ++ mkUnit ++ ") -> " ++ !(schExp i vs' sc)
    schConAlt i vs (MkConAlt (NS ["Prelude"] (UN "Nil")) tag args sc) = do
      let vs' = extendSVars args vs
      pure $ "([]) -> " ++ !(schExp i vs' sc)
    schConAlt i vs (MkConAlt (NS ["Prelude"] (UN "::")) tag args sc) = do
      let vs' = extendSVars args vs
      pure $ "([" ++ showSep " | " (drop 1 $ bindArgs 1 args vs') ++ "]) -> " ++ !(schExp i vs' sc)
    schConAlt i vs (MkConAlt (NS ["Lists", "ErlangPrelude"] (UN "Nil")) tag args sc) = do
      let vs' = extendSVars args vs
      pure $ "([]) -> " ++ !(schExp i vs' sc)
    schConAlt i vs (MkConAlt (NS ["Lists", "ErlangPrelude"] (UN "::")) tag args sc) = do
      let vs' = extendSVars args vs
      pure $ "([" ++ showSep " | " (drop 2 $ bindArgs 1 args vs') ++ "]) -> " ++ !(schExp i vs' sc)
    schConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple0")) tag args sc) = schConAltTuple 0 i vs args sc
    schConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple1")) tag args sc) = schConAltTuple 1 i vs args sc
    schConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple2")) tag args sc) = schConAltTuple 2 i vs args sc
    schConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple3")) tag args sc) = schConAltTuple 3 i vs args sc
    schConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple4")) tag args sc) = schConAltTuple 4 i vs args sc
    schConAlt i vs (MkConAlt (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple5")) tag args sc) = schConAltTuple 5 i vs args sc
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun0")) tag args sc) = schConAltFun i vs args sc 0 id
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun1")) tag args sc) = schConAltFun i vs args sc 1 id
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun2")) tag args sc) = schConAltFun i vs args sc 2 id
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun3")) tag args sc) = schConAltFun i vs args sc 3 id
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun4")) tag args sc) = schConAltFun i vs args sc 4 id
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun5")) tag args sc) = schConAltFun i vs args sc 5 id
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO0")) tag args sc) = schConAltFun i vs args sc 0 mkIOPure
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO1")) tag args sc) = schConAltFun i vs args sc 1 mkIOPure
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO2")) tag args sc) = schConAltFun i vs args sc 2 mkIOPure
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO3")) tag args sc) = schConAltFun i vs args sc 3 mkIOPure
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO4")) tag args sc) = schConAltFun i vs args sc 4 mkIOPure
    schConAlt i vs (MkConAlt (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO5")) tag args sc) = schConAltFun i vs args sc 5 mkIOPure
    schConAlt i vs (MkConAlt n tag args sc) = do
      let vs' = extendSVars args vs
      pure $ "({" ++ showSep ", " (show tag :: bindArgs 1 args vs') ++ "}) -> " ++ !(schExp i vs' sc)

    schConstAlt : Int -> SVars vars -> CConstAlt vars -> Core annot String
    schConstAlt i vs (MkConstAlt c exp) = pure $ "(" ++ schConstant c ++ ") -> " ++ !(schExp i vs exp)

    schConTuple : Int -> SVars vars -> List (CExp vars) -> Core annot String
    schConTuple i vs args = pure $ "{" ++ showSep ", " !(traverse (schExp i vs) args) ++ "}"

    -- Given an Idris function `idrisFun` with arity 2:
    -- 1. Uncurries this function according to arity: fun(X_1, X_2) -> (idrisFun(X1))(X_2) end
    -- 2. Transform the inner result with a user-defined function: fun(X_1, X_2) -> `transform`((idrisFun(X1))(X_2)) end
    -- The transformer is specifically used to perform the side-effects of the result (using `unsafePerformIO`)
    schConFun : Int -> SVars vars -> (arity : Nat) -> CExp vars -> (CExp vars -> CExp vars) -> Core annot String
    schConFun i vs arity func transformer = do
      let tempVars = take arity $ zipWith (\name, idx => name ++ show idx) (repeat "X_") [1..]
      let tempCRefs = take arity $ zipWith (\name, idx => CRef (MN name idx)) (repeat "X") [1..]
      let body = transformer (applyToArgs func tempCRefs)
      pure $ mkUncurriedFun tempVars !(schExp i vs body)

    schCon : Int -> SVars vars -> CExp vars -> Core annot String
    schCon i vs (CCon (NS ["Builtin"] (UN "MkUnit")) _ _) = pure mkUnit
    schCon i vs (CCon (NS ["Prelude"] (UN "Nil")) _ _) = pure "[]"
    schCon i vs (CCon (NS ["Prelude"] (UN "::")) _ [_, x, xs]) = pure $ "[" ++ !(schExp i vs x) ++ " | " ++ !(schExp i vs xs) ++ "]"
    schCon i vs (CCon (NS ["Lists", "ErlangPrelude"] (UN "Nil")) _ []) = pure "[]"
    schCon i vs (CCon (NS ["Lists", "ErlangPrelude"] (UN "::")) _ [_, _, x, xs]) = pure $ "[" ++ !(schExp i vs x) ++ " | " ++ !(schExp i vs xs) ++ "]"
    schCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple0")) _ []) = schConTuple i vs []
    schCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple1")) _ args) = schConTuple i vs (drop 1 args)
    schCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple2")) _ args) = schConTuple i vs (drop 2 args)
    schCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple3")) _ args) = schConTuple i vs (drop 3 args)
    schCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple4")) _ args) = schConTuple i vs (drop 4 args)
    schCon i vs (CCon (NS ["Tuples", "ErlangPrelude"] (UN "MkErlTuple5")) _ args) = schConTuple i vs (drop 5 args)
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun0")) _ args) = schConFun i vs 0 !(expectArgAtIndex 1 args) id
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun1")) _ args) = schConFun i vs 1 !(expectArgAtIndex 2 args) id
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun2")) _ args) = schConFun i vs 2 !(expectArgAtIndex 3 args) id
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun3")) _ args) = schConFun i vs 3 !(expectArgAtIndex 4 args) id
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun4")) _ args) = schConFun i vs 4 !(expectArgAtIndex 5 args) id
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlFun5")) _ args) = schConFun i vs 5 !(expectArgAtIndex 6 args) id
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO0")) _ args) = schConFun i vs 0 !(expectArgAtIndex 1 args) applyUnsafePerformIO
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO1")) _ args) = schConFun i vs 1 !(expectArgAtIndex 2 args) applyUnsafePerformIO
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO2")) _ args) = schConFun i vs 2 !(expectArgAtIndex 3 args) applyUnsafePerformIO
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO3")) _ args) = schConFun i vs 3 !(expectArgAtIndex 4 args) applyUnsafePerformIO
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO4")) _ args) = schConFun i vs 4 !(expectArgAtIndex 5 args) applyUnsafePerformIO
    schCon i vs (CCon (NS ["Functions", "ErlangPrelude"] (UN "MkErlIO5")) _ args) = schConFun i vs 5 !(expectArgAtIndex 6 args) applyUnsafePerformIO
    schCon i vs (CCon (NS ["Maps", "ErlangPrelude"] (UN "MkKeyValue")) _ [_, _, key, value]) = pure $ "#{" ++ !(schExp i vs key) ++ " => " ++ !(schExp i vs value) ++ "}"
    schCon i vs (CCon (NS ["Maps", "ErlangPrelude"] (UN "ErlMapNil")) _ _) = pure "#{}"
    schCon i vs (CCon (NS ["Maps", "ErlangPrelude"] (UN "ErlMapCons")) _ [x, xs]) = pure $ "maps:merge(" ++ !(schExp i vs xs) ++ ", " ++ !(schExp i vs x) ++ ")"
    schCon i vs (CCon x tag args) = pure $ schConstructor tag !(traverse (schExp i vs) args)
    schCon i vs tm = throw (InternalError ("Invalid constructor: " ++ show tm))
      
    -- oops, no traverse for Vect in Core
    schArgs : Int -> SVars vars -> Vect n (CExp vars) -> Core annot (Vect n String)
    schArgs i vs [] = pure []
    schArgs i vs (arg :: args) = pure $ !(schExp i vs arg) :: !(schArgs i vs args)

    export
    schExp : Int -> SVars vars -> CExp vars -> Core annot String
    schExp i vs (CLocal el) = pure $ lookupSVar el vs
    schExp i vs (CRef n) = pure $ schName n
    schExp i vs (CLam x sc) 
       = do let vs' = extendSVars [x] vs 
            sc' <- schExp i vs' sc
            pure $ "fun(" ++ lookupSVar Here vs' ++ ") -> " ++ sc' ++ " end"
    schExp i vs (CLet x val sc) 
       = do let vs' = extendSVars [x] vs
            val' <- schExp i vs val
            sc' <- schExp i vs' sc
            pure $ "(fun(" ++ lookupSVar Here vs' ++ ") -> " ++ sc' ++ " end(" ++ val' ++ "))"
    schExp i vs (CApp x args) 
        = pure $ "(" ++ !(schExp i vs x) ++ "(" ++ showSep ", " !(traverse (schExp i vs) args) ++ "))"
    schExp i vs con@(CCon x tag args)
        = schCon i vs con
    schExp i vs (COp op args) 
        = pure $ schOp op !(schArgs i vs args)
    schExp i vs (CExtPrim p args) 
        = schExtPrim i vs (toPrim p) args
    schExp i vs (CForce t) = pure $ "(" ++ !(schExp i vs t) ++ "())" -- TODO: Should use another mechanism to avoid evaluating delayed computation multiple times
    schExp i vs (CDelay t) = pure $ "fun() -> " ++ !(schExp i vs t) ++ " end"
    schExp i vs (CConCase sc alts def)
        = do tcode <- schExp i vs sc
             defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i vs v))) def
             conAlts <- traverse (schConAlt i vs) alts
             pure $ "(fun "
                     ++ showSep "; " (conAlts ++ schCaseDef defc)
                     ++ " end(" ++ tcode ++ "))"
    schExp i vs (CConstCase sc alts def)
        = do defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i vs v))) def
             tcode <- schExp i vs sc
             constAlts <- traverse (schConstAlt i vs) alts
             pure $ "(fun "
                      ++ showSep "; " (constAlts ++ schCaseDef defc)
                      ++ " end(blodwen_normalize_value(" ++ tcode ++ ")))"
    schExp i vs (CPrimVal c) = pure $ schConstant c
    schExp i vs CErased = pure "{}"
    schExp i vs (CCrash msg) = pure $ "throw(\"" ++ msg ++ "\")"

  -- Evaluate the outer `ErlList` to figure out the arity of the function call
  readArgs : Int -> SVars vars -> CExp vars -> Core annot (List String)
  readArgs i vs (CCon (NS ["Lists", "ErlangPrelude"] (UN "Nil")) _ []) = pure []
  readArgs i vs (CCon (NS ["Lists", "ErlangPrelude"] (UN "::")) _ [_, _, x, xs]) = pure $ !(schExp i vs x) :: !(readArgs i vs xs)
  readArgs i vs tm = throw (InternalError ("Unknown argument to foreign call: " ++ show tm))

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  schExtCommon : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  schExtCommon i vs ErlangCall [_, ret, CPrimVal (Str fn), args, world]
     = do parameterList <- readArgs i vs args
          pure $ mkWorld $ "(" ++ fn ++ "(" ++ showSep ", " parameterList ++ "))"
  schExtCommon i vs ErlangCall [_, ret, fn, args, world] -- TODO: Implement?
      = do pure $ mkWorld "false"
  schExtCommon i vs PutStr [arg, world] 
      = pure $ "(fun() -> io_unicode_put_str(" ++ !(schExp i vs arg) ++ "), " ++ mkWorld mkUnit ++ " end())"
  schExtCommon i vs GetStr [world] 
      = pure $ mkWorld "io_unicode_get_str(\"\")"
  schExtCommon i vs FileOpen [file, mode, bin, world]
      = pure $ mkWorld $ "blodwen_open("
                                      ++ !(schExp i vs file) ++ ", "
                                      ++ !(schExp i vs mode) ++ ", "
                                      ++ !(schExp i vs bin) ++ ")"
  schExtCommon i vs FileClose [file, world]
      = pure $ "(fun() -> blodwen_close(" ++ !(schExp i vs file) ++ "), " ++ mkWorld mkUnit ++ " end())"
  schExtCommon i vs FileReadLine [file, world]
      = pure $ mkWorld $ "blodwen_read_line(" ++ !(schExp i vs file) ++ ")"
  schExtCommon i vs FileWriteLine [file, str, world]
      = pure $ mkWorld $ "blodwen_write_line("
                                        ++ !(schExp i vs file) ++ ", "
                                        ++ !(schExp i vs str) ++ ")"
  schExtCommon i vs FileEOF [file, world]
      = pure $ mkWorld $ "blodwen_eof(" ++ !(schExp i vs file) ++ ")"
  schExtCommon i vs NewIORef [_, val, world]
      = pure $ mkWorld $ "(box " ++ !(schExp i vs val) ++ ")"
  schExtCommon i vs ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(unbox " ++ !(schExp i vs ref) ++ ")"
  schExtCommon i vs WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(set-box! " 
                           ++ !(schExp i vs ref) ++ " " 
                           ++ !(schExp i vs val) ++ ")"
  schExtCommon i vs (Unknown n) args 
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  schExtCommon i vs prim args 
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  schArglist : SVars ns -> String
  schArglist [] = ""
  schArglist [x] = x
  schArglist (x :: xs) = x ++ ", " ++ schArglist xs

  schDef : Name -> CDef -> Core annot String
  schDef n (MkFun args exp)
     = let vs = initSVars args in
           pure $ schName n ++ "(" ++ schArglist vs ++ ") -> "
                      ++ !(schExp 0 vs exp) ++ ".\n"
  schDef n (MkError exp)
     = pure $ schName n ++ "() -> " ++ !(schExp 0 [] exp) ++ ".\n"
  schDef n (MkCon t a) = pure "" -- Nothing to compile here
  
-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getScheme : (schExtPrim : {vars : _} -> Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String) ->
            Defs -> Name -> Core annot String
getScheme schExtPrim defs n
    = case lookupGlobalExact n (gamma defs) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just d => case compexpr d of
                          Nothing =>
                            throw (InternalError ("No compiled definition for " ++ show n))
                          Just d =>
                            schDef schExtPrim n d
