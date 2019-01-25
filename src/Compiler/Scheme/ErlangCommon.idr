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

export
mkWorld : String -> String
mkWorld res = schConstructor 0 ["false", res, "false"] -- PrimIO.MkIORes : {0 a : Type} -> a -> (1 x : %World) -> IORes a -- TODO: Is the `false`s necessary?

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

parameters (schExtPrim : {vars : _} -> Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String)
  mutual
    schConAlt : Int -> SVars vars -> CConAlt vars -> Core annot String
    schConAlt {vars} i vs (MkConAlt n tag args sc)
        = let vs' = extendSVars args vs in
              pure $ "({" ++ show tag
                          ++ bindArgs 1 args vs' !(schExp i vs' sc)
      where
        bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> String -> String
        bindArgs i [] vs body = "}) -> " ++ body
        bindArgs i (n :: ns) (v :: vs) body
            = ", " ++ v ++ bindArgs (i + 1) ns vs body

    schConstAlt : Int -> SVars vars -> CConstAlt vars -> Core annot String
    schConstAlt i vs (MkConstAlt c exp)
        = pure $ "(" ++ schConstant c ++ ") -> " ++ !(schExp i vs exp)
      
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
    schExp i vs (CCon x tag args) 
        = pure $ schConstructor tag !(traverse (schExp i vs) args)
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

  -- Evaluate the outer `FArgList` list to figure out the arity of the function call.
  -- Then let the runtime figure out the value of each parameter.
  -- TODO: Evaluate all parameters before giving them to the foreign function.
  readArgs : Int -> SVars vars -> CExp vars -> Core annot (List String)
  readArgs i vs (CCon (NS _ (UN "Nil")) _ []) = pure []
  readArgs i vs (CCon (NS _ (UN "::")) _ [_, arg, xs]) = pure $ ("blodwen_eval_arg(" ++ !(schExp i vs arg) ++ ")") :: !(readArgs i vs xs)
  readArgs i vs tm = throw (InternalError ("Unknown argument to foreign call: " ++ show tm))

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  schExtCommon : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  schExtCommon i vs ErlangCall [ret, CPrimVal (Str fn), args, world]
     = do parameterList <- readArgs i vs args
          pure $ mkWorld $ "(" ++ fn ++ "(" ++ showSep ", " parameterList ++ "))"
  schExtCommon i vs ErlangCall [ret, fn, args, world] -- TODO: Implement?
      = do pure $ mkWorld "false"
  schExtCommon i vs PutStr [arg, world] 
      = pure $ "(fun() -> io_unicode_put_str(" ++ !(schExp i vs arg) ++ "), " ++ mkWorld (schConstructor 0 []) ++ " end())" -- code for MkUnit
  schExtCommon i vs GetStr [world] 
      = pure $ mkWorld "io_unicode_get_str(\"\")"
  schExtCommon i vs FileOpen [file, mode, bin, world]
      = pure $ mkWorld $ "blodwen_open("
                                      ++ !(schExp i vs file) ++ ", "
                                      ++ !(schExp i vs mode) ++ ", "
                                      ++ !(schExp i vs bin) ++ ")"
  schExtCommon i vs FileClose [file, world]
      = pure $ "(fun() -> blodwen_close(" ++ !(schExp i vs file) ++ "), " ++ mkWorld (schConstructor 0 []) ++ " end())"
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
