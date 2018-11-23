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
data ExtPrim = CCall | SchemeCall | PutStr | GetStr 
             | FileOpen | FileClose | FileReadLine | FileWriteLine | FileEOF
             | NewIORef | ReadIORef | WriteIORef
             | Unknown Name

export
Show ExtPrim where
  show CCall = "CCall"
  show SchemeCall = "SchemeCall"
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
    = cond [(n == UN "prim__schemeCall", SchemeCall),
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

parameters (schExtPrim : {vars : _} -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String)
  mutual
    schConAlt : SVars vars -> CConAlt vars -> Core annot String
    schConAlt {vars} vs (MkConAlt n tag args sc)
        = let vs' = extendSVars args vs in
              pure $ "({" ++ show tag
                          ++ bindArgs 1 args vs' !(schExp vs' sc)
      where
        bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> String -> String
        bindArgs i [] vs body = "}) -> " ++ body
        bindArgs i (n :: ns) (v :: vs) body
            = ", " ++ v ++ bindArgs (i + 1) ns vs body

    schConstAlt : SVars vars -> CConstAlt vars -> Core annot String
    schConstAlt vs (MkConstAlt c exp)
        = pure $ "(" ++ schConstant c ++ ") -> " ++ !(schExp vs exp)
      
    -- oops, no traverse for Vect in Core
    schArgs : SVars vars -> Vect n (CExp vars) -> Core annot (Vect n String)
    schArgs vs [] = pure []
    schArgs vs (arg :: args) = pure $ !(schExp vs arg) :: !(schArgs vs args)

    export
    schExp : SVars vars -> CExp vars -> Core annot String
    schExp vs (CLocal el) = pure $ lookupSVar el vs
    schExp vs (CRef n) = pure $ schName n
    schExp vs (CLam x sc) 
       = do let vs' = extendSVars [x] vs 
            sc' <- schExp vs' sc
            pure $ "fun(" ++ lookupSVar Here vs' ++ ") -> " ++ sc' ++ " end"
    schExp vs (CLet x val sc) 
       = do let vs' = extendSVars [x] vs
            val' <- schExp vs val
            sc' <- schExp vs' sc
            pure $ "(fun(" ++ lookupSVar Here vs' ++ ") -> " ++ sc' ++ " end(" ++ val' ++ "))"
    schExp vs (CApp x args) 
        = pure $ "(" ++ !(schExp vs x) ++ "(" ++ showSep ", " !(traverse (schExp vs) args) ++ "))"
    schExp vs (CCon x tag args) 
        = pure $ schConstructor tag !(traverse (schExp vs) args)
    schExp vs (COp op args) 
        = pure $ schOp op !(schArgs vs args)
    schExp vs (CExtPrim p args) 
        = schExtPrim vs (toPrim p) args
    schExp vs (CForce t) = pure $ "(" ++ !(schExp vs t) ++ "())" -- TODO: Should use another mechanism to avoid evaluating delayed computation multiple times
    schExp vs (CDelay t) = pure $ "fun() -> " ++ !(schExp vs t) ++ " end"
    schExp vs (CConCase sc alts def)
        = do tcode <- schExp vs sc
             defc <- maybe (pure Nothing) (\v => pure (Just !(schExp vs v))) def
             conAlts <- traverse (schConAlt vs) alts
             pure $ "(fun "
                     ++ showSep "; " (conAlts ++ schCaseDef defc)
                     ++ " end(" ++ tcode ++ "))"
    schExp vs (CConstCase sc alts def)
        = do defc <- maybe (pure Nothing) (\v => pure (Just !(schExp vs v))) def
             tcode <- schExp vs sc
             constAlts <- traverse (schConstAlt vs) alts
             pure $ "(fun "
                      ++ showSep "; " (constAlts ++ schCaseDef defc)
                      ++ " end(blodwen_normalize_value(" ++ tcode ++ ")))"
    schExp vs (CPrimVal c) = pure $ schConstant c
    schExp vs CErased = pure "{}"
    schExp vs (CCrash msg) = pure $ "throw(\"" ++ msg ++ "\")"

  -- FIXME: Implement readArgs, fileOp, schExtCommon
  -- Need to convert the argument (a list of scheme arguments that may
  -- have been constructed at run time) to a scheme list to be passed to apply
  readArgs : SVars vars -> CExp vars -> Core annot String
  readArgs vs tm = pure $ "(blodwen-read-args " ++ !(schExp vs tm) ++ ")"

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  schExtCommon : SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  schExtCommon vs SchemeCall [ret, CPrimVal (Str fn), args, world]
     = pure $ mkWorld ("(apply " ++ fn ++" "
                  ++ !(readArgs vs args) ++ ")")
  schExtCommon vs SchemeCall [ret, fn, args, world]
       = pure $ mkWorld ("(apply (eval (string->symbol " ++ !(schExp vs fn) ++")) "
                    ++ !(readArgs vs args) ++ ")")
  schExtCommon vs PutStr [arg, world] 
      = pure $ "(fun() -> io_unicode_put_str(" ++ !(schExp vs arg) ++ "), " ++ mkWorld (schConstructor 0 []) ++ " end())" -- code for MkUnit
  schExtCommon vs GetStr [world] 
      = pure $ mkWorld "io_unicode_get_str(\"\")"
  schExtCommon vs FileOpen [file, mode, bin, world]
      = pure $ mkWorld $ "blodwen_open("
                                      ++ !(schExp vs file) ++ ", "
                                      ++ !(schExp vs mode) ++ ", "
                                      ++ !(schExp vs bin) ++ ")"
  schExtCommon vs FileClose [file, world]
      = pure $ "(fun() -> blodwen_close(" ++ !(schExp vs file) ++ "), " ++ mkWorld (schConstructor 0 []) ++ " end())"
  schExtCommon vs FileReadLine [file, world]
      = pure $ mkWorld $ "blodwen_read_line(" ++ !(schExp vs file) ++ ")"
  schExtCommon vs FileWriteLine [file, str, world]
      = pure $ mkWorld $ "blodwen_write_line("
                                        ++ !(schExp vs file) ++ ", "
                                        ++ !(schExp vs str) ++ ")"
  schExtCommon vs FileEOF [file, world]
      = pure $ mkWorld $ "blodwen_eof(" ++ !(schExp vs file) ++ ")"
  schExtCommon vs NewIORef [_, val, world]
      = pure $ mkWorld $ "(box " ++ !(schExp vs val) ++ ")"
  schExtCommon vs ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(unbox " ++ !(schExp vs ref) ++ ")"
  schExtCommon vs WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(set-box! " 
                           ++ !(schExp vs ref) ++ " " 
                           ++ !(schExp vs val) ++ ")"
  schExtCommon vs (Unknown n) args 
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  schExtCommon vs prim args 
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
                      ++ !(schExp vs exp) ++ ".\n"
  schDef n (MkError exp)
     = pure $ schName n ++ "() -> " ++ !(schExp [] exp) ++ ".\n"
  schDef n (MkCon t a) = pure "" -- Nothing to compile here
  
-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getScheme : (schExtPrim : {vars : _} -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String) ->
            Defs -> Name -> Core annot String
getScheme schExtPrim defs n
    = case lookupGlobalExact n (gamma defs) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just d => case compexpr d of
                          Nothing =>
                            throw (InternalError ("No compiled definition for " ++ show n))
                          Just d =>
                            schDef schExtPrim n d
