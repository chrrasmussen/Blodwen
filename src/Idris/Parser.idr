module Idris.Parser

import Core.Options
import Idris.Syntax
import public Parser.Support
import Parser.Lexer
import TTImp.TTImp

import public Text.Parser
import Data.List.Views

%default covering

-- Forward declare since they're used in the parser
topDecl : FileName -> IndentInfo -> Rule (List PDecl)
collectDefs : List PDecl -> List PDecl

public export
data EqOp = NoEq | EqOK

export
Eq EqOp where
  NoEq == NoEq = True
  EqOK == EqOK = True
  _ == _ = False

atom : FileName -> Rule PTerm
atom fname
    = do start <- location
         x <- constant
         end <- location
         pure (PPrimVal (MkFC fname start end) x)
  <|> do start <- location
         keyword "Type"
         end <- location
         pure (PType (MkFC fname start end))
  <|> do start <- location
         symbol "_"
         end <- location
         pure (PImplicit (MkFC fname start end))
  <|> do start <- location
         symbol "?"
         end <- location
         pure (PInfer (MkFC fname start end))
  <|> do start <- location
         x <- holeName
         end <- location
         pure (PHole (MkFC fname start end) False x)
  <|> do start <- location
         symbol "%"
         exactIdent "MkWorld"
         end <- location
         pure (PPrimVal (MkFC fname start end) WorldVal)
  <|> do start <- location
         symbol "%"
         exactIdent "World"
         end <- location
         pure (PPrimVal (MkFC fname start end) WorldType)
  <|> do start <- location
         symbol "%"
         exactIdent "search"
         end <- location
         pure (PSearch (MkFC fname start end) 1000)
  <|> do start <- location
         x <- name
         end <- location
         pure (PRef (MkFC fname start end) x)
  
whereBlock : FileName -> Int -> Rule (List PDecl)
whereBlock fname col
    = do keyword "where"
         ds <- blockAfter col (topDecl fname)
         pure (collectDefs (concat ds))

-- Expect a keyword, but if we get anything else it's a fatal error
commitKeyword : IndentInfo -> String -> Rule ()
commitKeyword indents req
    = do mustContinue indents (Just req)
         keyword req
         mustContinue indents Nothing

commitSymbol : String -> Rule ()
commitSymbol req
    = symbol req
       <|> fatalError ("Expected '" ++ req ++ "'")

continueWith : IndentInfo -> String -> Rule ()
continueWith indents req
    = do mustContinue indents (Just req)
         symbol req

iOperator : Rule Name
iOperator 
    = do n <- operator
         pure (UN n)
  <|> do symbol "`"
         n <- name
         symbol "`"
         pure n

mutual
  appExpr : FileName -> IndentInfo -> Rule PTerm
  appExpr fname indents
      = case_ fname indents
    <|> if_ fname indents
    <|> doBlock fname indents
    <|> do start <- location
           f <- simpleExpr fname indents
           args <- many (argExpr fname indents)
           end <- location
           pure (applyExpImp start end f args)
    <|> do start <- location
           op <- iOperator
           arg <- expr EqOK fname indents
           end <- location
           pure (PPrefixOp (MkFC fname start end) op arg)
    <|> fail "Expected 'case', 'if', 'do', application or operator expression"
    where
      applyExpImp : FilePos -> FilePos -> PTerm -> 
                    List (Either PTerm (Maybe Name, PTerm)) -> 
                    PTerm
      applyExpImp start end f [] = f
      applyExpImp start end f (Left exp :: args)
          = applyExpImp start end (PApp (MkFC fname start end) f exp) args
      applyExpImp start end f (Right (n, imp) :: args) 
          = applyExpImp start end (PImplicitApp (MkFC fname start end) f n imp) args

  argExpr : FileName -> IndentInfo -> 
            Rule (Either PTerm (Maybe Name, PTerm))
  argExpr fname indents
      = do continue indents
           arg <- simpleExpr fname indents
           the (EmptyRule _) $ case arg of
                PHole loc _ n => pure (Left (PHole loc True n))
                t => pure (Left t)
    <|> do continue indents
           arg <- implicitArg fname indents
           pure (Right arg)

  implicitArg : FileName -> IndentInfo -> Rule (Maybe Name, PTerm)
  implicitArg fname indents
      = do start <- location
           symbol "{"
           x <- unqualifiedName
           (do symbol "="
               commit
               tm <- expr EqOK fname indents
               symbol "}"
               pure (Just (UN x), tm))
             <|> (do symbol "}"
                     end <- location
                     pure (Just (UN x), PRef (MkFC fname start end) (UN x)))
    <|> do symbol "@{"
           commit
           tm <- expr EqOK fname indents
           symbol "}"
           pure (Nothing, tm)

  opExpr : EqOp -> FileName -> IndentInfo -> Rule PTerm
  opExpr q fname indents
      = do start <- location
           l <- appExpr fname indents
           (if q == EqOK
               then do continue indents
                       symbol "=" 
                       r <- opExpr EqOK fname indents
                       end <- location
                       pure (POp (MkFC fname start end) (UN "=") l r)
               else fail "= not allowed")
             <|> 
             (do continue indents
                 op <- iOperator
                 middle <- location
                 r <- opExpr q fname indents
                 end <- location
                 pure (POp (MkFC fname start end) op l r))
               <|> pure l

  dpair : FileName -> FilePos -> IndentInfo -> Rule PTerm
  dpair fname start indents
      = do x <- unqualifiedName
           symbol ":"
           ty <- expr EqOK fname indents
           loc <- location
           symbol "**"
           rest <- dpair fname loc indents <|> expr EqOK fname indents
           end <- location
           pure (PDPair (MkFC fname start end) 
                        (PRef (MkFC fname start loc) (UN x))
                        ty
                        rest)
    <|> do l <- expr EqOK fname indents
           loc <- location
           symbol "**"
           rest <- dpair fname loc indents <|> expr EqOK fname indents
           end <- location
           pure (PDPair (MkFC fname start end)
                        l
                        (PImplicit (MkFC fname start end))
                        rest)

  bracketedExpr : FileName -> FilePos -> IndentInfo -> Rule PTerm
  bracketedExpr fname start indents
      -- left section. This may also be a prefix operator, but we'll sort
      -- that out when desugaring: if the operator is infix, treat it as a
      -- section otherwise treat it as prefix
      = do op <- iOperator
           e <- expr EqOK fname indents
           continueWith indents ")"
           end <- location
           pure (PSectionL (MkFC fname start end) op e)
      -- unit type/value
    <|> do continueWith indents ")"
           end <- location
           pure (PUnit (MkFC fname start end))
      -- right section (1-tuple is just an expression)
    <|> do p <- dpair fname start indents
           symbol ")"
           pure p
    <|> do e <- expr EqOK fname indents
           (do op <- iOperator
               symbol ")"
               end <- location
               pure (PSectionR (MkFC fname start end) e op)
             <|>
            -- all the other bracketed expressions
            tuple fname start indents e)

  listExpr : FileName -> FilePos -> IndentInfo -> Rule PTerm
  listExpr fname start indents
      = do ret <- expr EqOK fname indents
           symbol "|"
           conds <- sepBy1 (symbol ",") (doAct fname indents)
           symbol "]"
           end <- location
           pure (PComprehension (MkFC fname start end) ret (concat conds))
    <|> do xs <- sepBy (symbol ",") (expr EqOK fname indents)
           symbol "]"
           end <- location
           pure (PList (MkFC fname start end) xs)
           

  -- A pair, dependent pair, or just a single expression
  tuple : FileName -> FilePos -> IndentInfo -> PTerm -> Rule PTerm
  tuple fname start indents e
      = do rest <- some (do symbol ","
                            estart <- location
                            el <- expr EqOK fname indents
                            pure (estart, el))
           continueWith indents ")"
           end <- location
           pure (PPair (MkFC fname start end) e
                       (mergePairs end rest))
     <|> do continueWith indents ")"
            end <- location
            pure (PBracketed (MkFC fname start end) e)
    where
      mergePairs : FilePos -> List (FilePos, PTerm) -> PTerm
      mergePairs end [] = PUnit (MkFC fname start end)
      mergePairs end [(estart, exp)] = exp
      mergePairs end ((estart, exp) :: rest)
          = PPair (MkFC fname estart end) exp (mergePairs end rest)

  simpleExpr : FileName -> IndentInfo -> Rule PTerm
  simpleExpr fname indents
      = do start <- location
           x <- unqualifiedName
           symbol "@"
           commit
           expr <- simpleExpr fname indents
           end <- location
           pure (PAs (MkFC fname start end) (UN x) expr)
    <|> atom fname
    <|> binder fname indents
    <|> rewrite_ fname indents
    <|> record_ fname indents
    <|> do start <- location
           symbol ".("
           commit
           e <- expr EqOK fname indents
           symbol ")"
           end <- location
           pure (PDotted (MkFC fname start end) e)
    <|> do start <- location
           symbol "`("
           e <- expr EqOK fname indents
           symbol ")"
           end <- location
           pure (PQuote (MkFC fname start end) e)
    <|> do start <- location
           symbol "~"
           e <- simpleExpr fname indents
           end <- location
           pure (PUnquote (MkFC fname start end) e)
    <|> do start <- location
           symbol "("
           bracketedExpr fname start indents
    <|> do start <- location
           symbol "["
           listExpr fname start indents
  
  multiplicity : EmptyRule (Maybe Integer)
  multiplicity
      = do c <- intLit
           pure (Just c)
    <|> do symbol "&"
           pure (Just 2)
    <|> pure Nothing

  getMult : Maybe Integer -> EmptyRule RigCount
  getMult (Just 0) = pure Rig0
  getMult (Just 1) = pure (Rig1 False)
  getMult (Just 2) = pure (Rig1 True)
  getMult Nothing = pure RigW
  getMult _ = fatalError "Invalid multiplicity (must be 0 or 1)"

  pibindAll : FC -> PiInfo -> List (RigCount, Maybe Name, PTerm) -> 
              PTerm -> PTerm
  pibindAll fc p [] scope = scope
  pibindAll fc p ((rig, n, ty) :: rest) scope
           = PPi fc rig p n ty (pibindAll fc p rest scope)

  bindList : FileName -> FilePos -> IndentInfo -> 
             Rule (List (RigCount, Name, PTerm))
  bindList fname start indents
      = sepBy1 (symbol ",")
               (do rigc <- multiplicity
                   n <- unqualifiedName
                   ty <- option 
                            (PInfer (MkFC fname start start))
                            (do symbol ":"
                                opExpr EqOK fname indents)
                   rig <- getMult rigc
                   pure (rig, UN n, ty))

  pibindList : FileName -> FilePos -> IndentInfo -> 
               Rule (List (RigCount, Maybe Name, PTerm))
  pibindList fname start indents
       = do rigc <- multiplicity
            ns <- sepBy1 (symbol ",") unqualifiedName
            symbol ":"
            ty <- expr EqOK fname indents
            atEnd indents
            rig <- getMult rigc
            pure (map (\n => (rig, Just (UN n), ty)) ns)
     <|> sepBy1 (symbol ",")
                (do rigc <- multiplicity
                    n <- name
                    symbol ":"
                    ty <- expr EqOK fname indents
                    rig <- getMult rigc
                    pure (rig, Just n, ty))
      
  bindSymbol : Rule PiInfo
  bindSymbol
      = do symbol "->"
           pure Explicit
    <|> do symbol "=>"
           pure AutoImplicit


  explicitPi : FileName -> IndentInfo -> Rule PTerm
  explicitPi fname indents
      = do start <- location
           symbol "("
           binders <- pibindList fname start indents
           symbol ")"
           exp <- bindSymbol
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) exp binders scope)

  autoImplicitPi : FileName -> IndentInfo -> Rule PTerm
  autoImplicitPi fname indents
      = do start <- location
           symbol "{"
           keyword "auto"
           commit
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) AutoImplicit binders scope)

  forall_ : FileName -> IndentInfo -> Rule PTerm
  forall_ fname indents
      = do start <- location
           keyword "forall"
           commit
           nstart <- location
           ns <- sepBy1 (symbol ",") unqualifiedName
           nend <- location
           let nfc = MkFC fname nstart nend
           let binders = map (\n => (Rig0, Just (UN n), PImplicit nfc)) ns
           symbol "."
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) Implicit binders scope)

  implicitPi : FileName -> IndentInfo -> Rule PTerm
  implicitPi fname indents
      = do start <- location
           symbol "{"
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) Implicit binders scope)

  lam : FileName -> IndentInfo -> Rule PTerm
  lam fname indents
      = do start <- location
           symbol "\\"
           binders <- bindList fname start indents
           symbol "=>"
           mustContinue indents Nothing
           scope <- expr EqOK fname indents
           end <- location
           pure (bindAll (MkFC fname start end) binders scope)
     where
       bindAll : FC -> List (RigCount, Name, PTerm) -> PTerm -> PTerm
       bindAll fc [] scope = scope
       bindAll fc ((rig, n, ty) :: rest) scope
           = PLam fc rig Explicit n ty (bindAll fc rest scope)

  letBinder : FileName -> IndentInfo -> 
              Rule (FilePos, FilePos, RigCount, PTerm, PTerm, List PClause)
  letBinder fname indents
      = do start <- location
           rigc <- multiplicity
           pat <- expr NoEq fname indents
           symbol "="
           val <- expr EqOK fname indents
           alts <- block (patAlt fname)
           end <- location
           rig <- getMult rigc
           pure (start, end, rig, pat, val, alts)

  buildLets : FileName ->
              List (FilePos, FilePos, RigCount, PTerm, PTerm, List PClause) ->
              PTerm -> PTerm
  buildLets fname [] sc = sc
  buildLets fname ((start, end, rig, pat, val, alts) :: rest) sc
      = let fc = MkFC fname start end in
            PLet fc rig pat (PImplicit fc) val 
                 (buildLets fname rest sc) alts

  buildDoLets : FileName ->
                List (FilePos, FilePos, RigCount, PTerm, PTerm, List PClause) ->
                List PDo
  buildDoLets fname [] = []
  buildDoLets fname ((start, end, rig, PRef fc' (UN n), val, []) :: rest)
      = let fc = MkFC fname start end in
            if lowerFirst n
               then DoLet fc (UN n) rig val :: buildDoLets fname rest
               else DoLetPat fc (PRef fc' (UN n)) val [] 
                         :: buildDoLets fname rest
  buildDoLets fname ((start, end, rig, pat, val, alts) :: rest)
      = let fc = MkFC fname start end in
            DoLetPat fc pat val alts :: buildDoLets fname rest

  let_ : FileName -> IndentInfo -> Rule PTerm
  let_ fname indents
      = do start <- location
           keyword "let"
           res <- nonEmptyBlock (letBinder fname) 
           commitKeyword indents "in"
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (buildLets fname res scope)
                
    <|> do start <- location
           keyword "let"
           commit
           ds <- nonEmptyBlock (topDecl fname)
           commitKeyword indents "in"
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (PLocal (MkFC fname start end) (collectDefs (concat ds)) scope)

  case_ : FileName -> IndentInfo -> Rule PTerm
  case_ fname indents
      = do start <- location
           keyword "case"
           scr <- expr EqOK fname indents
           commitKeyword indents "of"
           alts <- block (caseAlt fname)
           end <- location
           pure (PCase (MkFC fname start end) scr alts)

  caseAlt : FileName -> IndentInfo -> Rule PClause
  caseAlt fname indents
      = do start <- location
           lhs <- opExpr NoEq fname indents
           caseRHS fname start indents lhs
          
  caseRHS : FileName -> FilePos -> IndentInfo -> PTerm -> Rule PClause
  caseRHS fname start indents lhs
      = do symbol "=>"
           mustContinue indents Nothing
           rhs <- expr EqOK fname indents
           atEnd indents 
           end <- location
           pure (MkPatClause (MkFC fname start end) lhs rhs [])
    <|> do keyword "impossible"
           atEnd indents
           end <- location
           pure (MkImpossible (MkFC fname start end) lhs)

  if_ : FileName -> IndentInfo -> Rule PTerm
  if_ fname indents
      = do start <- location
           keyword "if"
           x <- expr EqOK fname indents
           commitKeyword indents "then"
           t <- expr EqOK fname indents
           commitKeyword indents "else"
           e <- expr EqOK fname indents
           atEnd indents
           end <- location
           pure (PIfThenElse (MkFC fname start end) x t e)

  record_ : FileName -> IndentInfo -> Rule PTerm
  record_ fname indents
      = do start <- location
           keyword "record"
           commit
           symbol "{"
           fs <- sepBy1 (symbol ",") (field fname indents)
           symbol "}"
           end <- location
           pure (PUpdate (MkFC fname start end) fs)

  field : FileName -> IndentInfo -> Rule PFieldUpdate
  field fname indents
      = do path <- sepBy1 (symbol "->") unqualifiedName
           upd <- (do symbol "="; pure PSetField)
                      <|>
                  (do symbol "$="; pure PSetFieldApp)
           val <- opExpr NoEq fname indents
           pure (upd path val)

  rewrite_ : FileName -> IndentInfo -> Rule PTerm
  rewrite_ fname indents
      = do start <- location
           keyword "rewrite"
           rule <- expr EqOK fname indents
           commitKeyword indents "in"
           tm <- expr EqOK fname indents
           end <- location
           pure (PRewrite (MkFC fname start end) rule tm)
  
  doBlock : FileName -> IndentInfo -> Rule PTerm
  doBlock fname indents
      = do start <- location
           keyword "do"
           actions <- block (doAct fname)
           end <- location
           pure (PDoBlock (MkFC fname start end) (concat actions))

  lowerFirst : String -> Bool
  lowerFirst "" = False
  lowerFirst str = assert_total (isLower (strHead str))

  validPatternVar : Name -> EmptyRule ()
  validPatternVar (UN n)
      = if lowerFirst n then pure ()
                        else fail "Not a pattern variable"
  validPatternVar _ = fail "Not a pattern variable"

  doAct : FileName -> IndentInfo -> Rule (List PDo)
  doAct fname indents
      = do start <- location
           n <- name
           -- If the name doesn't begin with a lower case letter, we should
           -- treat this as a pattern, so fail
           validPatternVar n
           symbol "<-"
           val <- expr EqOK fname indents
           atEnd indents
           end <- location
           pure [DoBind (MkFC fname start end) n val]
    <|> do keyword "let"
           res <- block (letBinder fname)
           atEnd indents
           pure (buildDoLets fname res)
    <|> do start <- location
           keyword "let"
           res <- block (topDecl fname)
           end <- location
           atEnd indents
           pure [DoLetLocal (MkFC fname start end) (concat res)]
    <|> do start <- location
           keyword "rewrite"
           rule <- expr EqOK fname indents
           atEnd indents
           end <- location
           pure [DoRewrite (MkFC fname start end) rule]
    <|> do start <- location
           e <- expr NoEq fname indents
           (do atEnd indents
               end <- location
               pure [DoExp (MkFC fname start end) e])
             <|> (do symbol "<-"
                     val <- expr EqOK fname indents
                     alts <- block (patAlt fname)
                     atEnd indents
                     end <- location
                     pure [DoBindPat (MkFC fname start end) e val alts])

  patAlt : FileName -> IndentInfo -> Rule PClause
  patAlt fname indents
      = do symbol "|"
           caseAlt fname indents

  binder : FileName -> IndentInfo -> Rule PTerm
  binder fname indents
      = let_ fname indents
    <|> autoImplicitPi fname indents
    <|> forall_ fname indents
    <|> implicitPi fname indents
    <|> explicitPi fname indents
    <|> lam fname indents

  typeExpr : EqOp -> FileName -> IndentInfo -> Rule PTerm
  typeExpr q fname indents
      = do start <- location
           arg <- opExpr q fname indents
           (do continue indents
               rest <- some (do exp <- bindSymbol
                                op <- opExpr EqOK fname indents
                                pure (exp, op))
               end <- location
               pure (mkPi start end arg rest))
             <|> pure arg
    where
      mkPi : FilePos -> FilePos -> PTerm -> List (PiInfo, PTerm) -> PTerm
      mkPi start end arg [] = arg
      mkPi start end arg ((exp, a) :: as) 
            = PPi (MkFC fname start end) RigW exp Nothing arg 
                  (mkPi start end a as)

  export
  expr : EqOp -> FileName -> IndentInfo -> Rule PTerm
  expr = typeExpr

visOption : Rule Visibility
visOption
    = do keyword "public"
         keyword "export"
         pure Public
  <|> do keyword "export"
         pure Export
  <|> do keyword "private"
         pure Private

visibility : EmptyRule Visibility
visibility
    = visOption
  <|> pure Private

tyDecl : FileName -> IndentInfo -> Rule PTypeDecl
tyDecl fname indents
    = do start <- location
         n <- name
         symbol ":"
         mustWork $
            do ty <- expr EqOK fname indents
               end <- location
               atEnd indents
               pure (MkPTy (MkFC fname start end) n ty)

mutual
  parseRHS : (withArgs : Nat) ->
             FileName -> FilePos -> Int ->
             IndentInfo -> (lhs : PTerm) -> Rule PClause
  parseRHS withArgs fname start col indents lhs
       = do symbol "="
            mustWork $
              do rhs <- expr EqOK fname indents
                 ws <- option [] (whereBlock fname col)
                 atEnd indents
                 end <- location
                 pure (MkPatClause (MkFC fname start end) lhs rhs ws)
     <|> do keyword "with"
            wstart <- location
            symbol "("
            wval <- bracketedExpr fname wstart indents
            ws <- nonEmptyBlock (clause (S withArgs) fname)
            end <- location
            pure (MkWithClause (MkFC fname start end) lhs wval ws)
     <|> do keyword "impossible"
            atEnd indents
            end <- location
            pure (MkImpossible (MkFC fname start end) lhs)

  clause : Nat -> FileName -> IndentInfo -> Rule PClause
  clause withArgs fname indents
      = do start <- location
           col <- column
           lhs <- expr NoEq fname indents
           extra <- many parseWithArg
           if (withArgs /= length extra)
              then fatalError "Wrong number of 'with' arguments"
              else parseRHS withArgs fname start col indents (applyArgs lhs extra)
    where
      applyArgs : PTerm -> List (FC, PTerm) -> PTerm
      applyArgs f [] = f
      applyArgs f ((fc, a) :: args) = applyArgs (PApp fc f a) args

      parseWithArg : Rule (FC, PTerm)
      parseWithArg 
          = do symbol "|"
               start <- location
               tm <- expr NoEq fname indents
               end <- location
               pure (MkFC fname start end, tm)

mkTyConType : FC -> List Name -> PTerm
mkTyConType fc [] = PType fc
mkTyConType fc (x :: xs) 
   = PPi fc rig1 Explicit Nothing (PType fc) (mkTyConType fc xs)

mkDataConType : FC -> PTerm -> List (Either PTerm (Maybe Name, PTerm)) -> PTerm
mkDataConType fc ret [] = ret
mkDataConType fc ret (Left x :: xs)
    = PPi fc rig1 Explicit Nothing x (mkDataConType fc ret xs)
mkDataConType fc ret (Right (n, PRef fc' x) :: xs)
    = if n == Just x
         then PPi fc rig1 Implicit n (PType fc') 
                          (mkDataConType fc ret xs)
         else PPi fc rig1 Implicit n (PRef fc' x) 
                          (mkDataConType fc ret xs)
mkDataConType fc ret (Right (n, x) :: xs)
    = PPi fc rig1 Implicit n x (mkDataConType fc ret xs)

simpleCon : FileName -> PTerm -> IndentInfo -> Rule PTypeDecl
simpleCon fname ret indents
    = do start <- location
         cname <- name
         params <- many (argExpr fname indents)
         atEnd indents
         end <- location
         let cfc = MkFC fname start end
         pure (MkPTy cfc cname (mkDataConType cfc ret params)) 

simpleData : FileName -> FilePos -> Name -> IndentInfo -> Rule PDataDecl
simpleData fname start n indents
    = do params <- many name
         tyend <- location
         let tyfc = MkFC fname start tyend
         symbol "="
         let conRetTy = papply tyfc (PRef tyfc n)
                           (map (PRef tyfc) params)
         cons <- sepBy1 (symbol "|") 
                        (simpleCon fname conRetTy indents)
         end <- location
         pure (MkPData (MkFC fname start end) n
                       (mkTyConType tyfc params) [] cons)

dataOpt : Rule DataOpt
dataOpt
    = do exactIdent "noHints"
         pure NoHints
  <|> do exactIdent "search"
         ns <- some name
         pure (SearchBy ns)

dataBody : FileName -> Int -> FilePos -> Name -> IndentInfo -> PTerm -> 
           EmptyRule PDataDecl
dataBody fname mincol start n indents ty
    = do atEnd indents
         end <- location
         pure (MkPLater (MkFC fname start end) n ty)
  <|> do keyword "where"
         opts <- option [] (do symbol "["
                               dopts <- sepBy1 (symbol ",") dataOpt
                               symbol "]"
                               pure dopts)
         cs <- blockAfter mincol (tyDecl fname)
         end <- location
         pure (MkPData (MkFC fname start end) n ty opts cs)

gadtData : FileName -> Int -> FilePos -> Name -> IndentInfo -> Rule PDataDecl
gadtData fname mincol start n indents
    = do symbol ":"
         commit
         ty <- expr EqOK fname indents
         dataBody fname mincol start n indents ty

dataDeclBody : FileName -> IndentInfo -> Rule PDataDecl
dataDeclBody fname indents
    = do start <- location
         col <- column
         keyword "data"
         n <- name
         simpleData fname start n indents 
           <|> gadtData fname col start n indents

dataDecl : FileName -> IndentInfo -> Rule PDecl
dataDecl fname indents
    = do start <- location
         vis <- visibility
         dat <- dataDeclBody fname indents
         end <- location
         pure (PData (MkFC fname start end) vis dat)

stripBraces : String -> String
stripBraces str = substr 3 (length str `minus` (3 * 2)) str

onoff : Rule Bool
onoff 
   = do exactIdent "on" 
        pure True
 <|> do exactIdent "off"
        pure False

extension : Rule LangExt
extension
    = do exactIdent "Borrowing"
         pure Borrowing

directive : FileName -> IndentInfo -> Rule Directive
directive fname indents
    = do exactIdent "hide"
         n <- name
         atEnd indents
         pure (Hide False n)
  <|> do exactIdent "hide_export"
         n <- name
         atEnd indents
         pure (Hide True n)
  <|> do exactIdent "logging"
         lvl <- intLit
         atEnd indents
         pure (Logging (cast lvl))
  <|> do exactIdent "lazy"
         ty <- name
         d <- name
         f <- name
         i <- name
         atEnd indents
         pure (LazyNames ty d f i)
  <|> do exactIdent "auto_lazy"
         b <- onoff
         atEnd indents
         pure (LazyOn b)
  <|> do exactIdent "pair"
         ty <- name
         f <- name
         s <- name
         atEnd indents
         pure (PairNames ty f s)
  <|> do keyword "rewrite"
         eq <- name
         rw <- name
         atEnd indents
         pure (RewriteName eq rw)
  <|> do exactIdent "integerLit"
         n <- name
         atEnd indents
         pure (PrimInteger n)
  <|> do exactIdent "stringLit"
         n <- name
         atEnd indents
         pure (PrimString n)
  <|> do exactIdent "charLit"
         n <- name
         atEnd indents
         pure (PrimChar n)
  <|> do exactIdent "name"
         n <- name
         ns <- sepBy1 (symbol ",") unqualifiedName
         atEnd indents
         pure (Names n ns)
  <|> do exactIdent "start"
         e <- expr EqOK fname indents
         atEnd indents
         pure (StartExpr e)
  <|> do exactIdent "allow_overloads"
         n <- name
         atEnd indents
         pure (Overloadable n)
  <|> do exactIdent "language"
         e <- extension
         atEnd indents
         pure (Extension e)

fix : Rule Fixity
fix
    = do keyword "infixl"; pure InfixL
  <|> do keyword "infixr"; pure InfixR
  <|> do keyword "infix"; pure Infix
  <|> do keyword "prefix"; pure Prefix

namespaceHead : Rule (List String)
namespaceHead 
    = do keyword "namespace"
         commit
         ns <- namespace_
         pure ns

namespaceDecl : FileName -> IndentInfo -> Rule PDecl
namespaceDecl fname indents
    = do start <- location
         ns <- namespaceHead
         end <- location
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         pure (PNamespace (MkFC fname start end) ns (concat ds))

mutualDecls : FileName -> IndentInfo -> Rule PDecl
mutualDecls fname indents
    = do start <- location
         keyword "mutual"
         commit
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         end <- location
         pure (PMutual (MkFC fname start end) (concat ds))

paramDecls : FileName -> IndentInfo -> Rule PDecl
paramDecls fname indents
    = do start <- location
         keyword "parameters"
         commit
         symbol "("
         ps <- some (do x <- unqualifiedName
                        symbol ":"
                        ty <- typeExpr EqOK fname indents
                        pure (UN x, ty))
         symbol ")"
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         end <- location
         pure (PParameters (MkFC fname start end) ps (collectDefs (concat ds)))

fnOpt : Rule FnOpt
fnOpt
    = do keyword "partial"
         pure PartialOK
  <|> do keyword "total"
         pure Total
  <|> do keyword "covering"
         pure Covering

fnDirectOpt : Rule FnOpt
fnDirectOpt
    = do exactIdent "hint"
         pure (Hint True)
  <|> do exactIdent "globalhint"
         pure (GlobalHint True)
  <|> do exactIdent "defaulthint"
         pure (GlobalHint False)
  <|> do exactIdent "inline"
         pure Inline
  <|> do exactIdent "extern"
         pure ExternFn

visOpt : Rule (Either Visibility FnOpt)
visOpt
    = do vis <- visOption
         pure (Left vis)
  <|> do tot <- fnOpt
         pure (Right tot)
  <|> do symbol "%"
         opt <- fnDirectOpt
         pure (Right opt)

getVisibility : Maybe Visibility -> List (Either Visibility FnOpt) -> 
                EmptyRule Visibility
getVisibility Nothing [] = pure Private
getVisibility (Just vis) [] = pure vis
getVisibility Nothing (Left x :: xs) = getVisibility (Just x) xs
getVisibility (Just vis) (Left x :: xs)
   = fatalError "Multiple visibility modifiers"
getVisibility v (_ :: xs) = getVisibility v xs

getRight : Either a b -> Maybe b
getRight (Left _) = Nothing
getRight (Right v) = Just v

constraints : FileName -> IndentInfo -> EmptyRule (List (Maybe Name, PTerm))
constraints fname indents
    = do tm <- appExpr fname indents
         symbol "=>"
         more <- constraints fname indents
         pure ((Nothing, tm) :: more)
  <|> do symbol "("
         n <- name
         symbol ":"
         tm <- expr EqOK fname indents
         symbol ")"
         symbol "=>"
         more <- constraints fname indents
         pure ((Just n, tm) :: more)
  <|> pure []

ifaceParam : FileName -> IndentInfo -> Rule (Name, PTerm)
ifaceParam fname indents
    = do symbol "("
         n <- name
         symbol ":"
         tm <- expr EqOK fname indents
         symbol ")"
         pure (n, tm)
  <|> do start <- location
         n <- name
         end <- location
         pure (n, PInfer (MkFC fname start end))

ifaceDecl : FileName -> IndentInfo -> Rule PDecl
ifaceDecl fname indents
    = do start <- location
         vis <- visibility
         col <- column
         keyword "interface"
         commit
         cons <- constraints fname indents
         n <- name
         params <- many (ifaceParam fname indents)
         det <- option [] (do symbol "|"
                              sepBy (symbol ",") name)
         keyword "where"
         dc <- option Nothing (do exactIdent "constructor"
                                  n <- name
                                  pure (Just n))
         body <- assert_total (blockAfter col (topDecl fname))
         end <- location
         pure (PInterface (MkFC fname start end) 
                      vis cons n params det dc (collectDefs (concat body)))

implDecl : FileName -> IndentInfo -> Rule PDecl
implDecl fname indents
    = do start <- location
         vis <- visibility
         col <- column
         option () (keyword "implementation")
         iname <- option Nothing (do symbol "["
                                     iname <- name
                                     symbol "]"
                                     pure (Just iname))
         cons <- constraints fname indents
         n <- name
         params <- many (simpleExpr fname indents)
         body <- optional (do keyword "where"
                              blockAfter col (topDecl fname))
         atEnd indents
         end <- location
         pure (PImplementation (MkFC fname start end)
                         vis Single cons n params iname 
                         (map (collectDefs . concat) body))

fieldDecl : FileName -> IndentInfo -> Rule (List PField)
fieldDecl fname indents
      = do symbol "{"
           commit
           fs <- fieldBody Implicit
           symbol "}"
           atEnd indents
           pure fs
    <|> do fs <- fieldBody Explicit
           atEnd indents
           pure fs
  where
    fieldBody : PiInfo -> Rule (List PField)
    fieldBody p
        = do start <- location
             ns <- sepBy1 (symbol ",") unqualifiedName
             symbol ":"
             ty <- expr EqOK fname indents
             end <- location
             pure (map (\n => MkField (MkFC fname start end)
                                      rig1 p (UN n) ty) ns)

recordDecl : FileName -> IndentInfo -> Rule PDecl
recordDecl fname indents
    = do start <- location
         vis <- visibility
         col <- column
         keyword "record"
         commit
         n <- name
         params <- many (ifaceParam fname indents)
         keyword "where"
         dc <- option Nothing (do exactIdent "constructor"
                                  n <- name
                                  pure (Just n))
         flds <- assert_total (blockAfter col (fieldDecl fname))
         end <- location
         pure (PRecord (MkFC fname start end) 
                       vis n params dc (concat flds))

claim : FileName -> IndentInfo -> Rule PDecl
claim fname indents
    = do start <- location
         visOpts <- many visOpt
         vis <- getVisibility Nothing visOpts
         let opts = mapMaybe getRight visOpts
         cl <- tyDecl fname indents
         end <- location
         pure (PClaim (MkFC fname start end) vis opts cl)
         
definition : FileName -> IndentInfo -> Rule PDecl
definition fname indents
    = do start <- location
         nd <- clause 0 fname indents
         end <- location
         pure (PDef (MkFC fname start end) [nd])

fixDecl : FileName -> IndentInfo -> Rule (List PDecl)
fixDecl fname indents
    = do start <- location
         fixity <- fix
         commit
         prec <- intLit
         ops <- sepBy1 (symbol ",") iOperator
         end <- location
         pure (map (PFixity (MkFC fname start end) fixity (cast prec)) ops)

directiveDecl : FileName -> IndentInfo -> Rule PDecl
directiveDecl fname indents
    = do start <- location
         symbol "%" 
         (do d <- directive fname indents
             end <- location
             pure (PDirective (MkFC fname start end) d))
           <|>
          (do exactIdent "runElab"
              tm <- expr EqOK fname indents
              end <- location
              atEnd indents
              pure (PReflect (MkFC fname start end) tm))

-- Declared at the top
-- topDecl : FileName -> IndentInfo -> Rule (List PDecl)
topDecl fname indents
    = do d <- dataDecl fname indents
         pure [d]
  <|> do d <- claim fname indents
         pure [d]
  <|> do d <- definition fname indents
         pure [d]
  <|> fixDecl fname indents
  <|> do d <- ifaceDecl fname indents
         pure [d]
  <|> do d <- implDecl fname indents
         pure [d]
  <|> do d <- recordDecl fname indents
         pure [d]
  <|> do d <- namespaceDecl fname indents
         pure [d]
  <|> do d <- mutualDecls fname indents
         pure [d]
  <|> do d <- paramDecls fname indents
         pure [d]
  <|> do d <- directiveDecl fname indents
         pure [d]
  <|> do start <- location
         dstr <- terminal "Expected CG directive"
                          (\x => case tok x of
                                      CGDirective d => Just d
                                      _ => Nothing)
         end <- location
         let cgrest = span isAlphaNum dstr
         pure [PDirective (MkFC fname start end)
                (CGAction (fst cgrest) (stripBraces (trim (snd cgrest))))]
  <|> fatalError "Couldn't parse declaration"

-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses into one definition. This might mean merging two
-- functions which are different, if there are forward declarations,
-- but we'll split them in Desugar.idr. We can't do this now, because we
-- haven't resolved operator precedences yet.
-- Declared at the top.
-- collectDefs : List PDecl -> List PDecl
collectDefs [] = []
collectDefs (PDef annot cs :: ds)
    = let (cs', rest) = spanMap isClause ds in
          PDef annot (cs ++ cs') :: assert_total (collectDefs rest)
  where
    spanMap : (a -> Maybe (List b)) -> List a -> (List b, List a)
    spanMap f [] = ([], [])
    spanMap f (x :: xs) = case f x of
                               Nothing => ([], x :: xs)
                               Just y => case spanMap f xs of
                                              (ys, zs) => (y ++ ys, zs)

    isClause : PDecl -> Maybe (List PClause)
    isClause (PDef annot cs) 
        = Just cs 
    isClause _ = Nothing
collectDefs (PNamespace annot ns nds :: ds)
    = PNamespace annot ns (collectDefs nds) :: collectDefs ds
collectDefs (PMutual annot nds :: ds)
    = PMutual annot (collectDefs nds) :: collectDefs ds
collectDefs (d :: ds)
    = d :: collectDefs ds

export
import_ : FileName -> IndentInfo -> Rule Import
import_ fname indents
    = do start <- location
         keyword "import"
         reexp <- option False (do keyword "public"
                                   pure True)
         ns <- namespace_
         nsAs <- option ns (do exactIdent "as"
                               namespace_)
         end <- location
         atEnd indents
         pure (MkImport (MkFC fname start end) reexp ns nsAs)

export
prog : FileName -> Rule Module
prog fname
    = do start <- location
         nspace <- option ["Main"]
                      (do keyword "module"
                          namespace_)
         end <- location
         imports <- block (import_ fname)
         ds <- nonEmptyBlock (topDecl fname)
         pure (MkModule (MkFC fname start end)
                        nspace imports (collectDefs (concat ds)))

export
progHdr : FileName -> EmptyRule Module
progHdr fname
    = do start <- location
         nspace <- option ["Main"]
                      (do keyword "module"
                          namespace_)
         end <- location
         imports <- block (import_ fname)
         pure (MkModule (MkFC fname start end)
                        nspace imports [])

parseMode : Rule REPLEval
parseMode
     = do exactIdent "typecheck"
          pure EvalTC
   <|> do exactIdent "tc"
          pure EvalTC
   <|> do exactIdent "normalise"
          pure NormaliseAll
   <|> do exactIdent "normalize" -- oh alright then
          pure NormaliseAll
   <|> do exactIdent "execute"
          pure Execute
   <|> do exactIdent "exec"
          pure Execute

setVarOption : Rule REPLOpt
setVarOption
    = do exactIdent "eval"
         mode <- parseMode
         pure (EvalMode mode)
  <|> do exactIdent "editor"
         e <- unqualifiedName 
         pure (Editor e)
  <|> do exactIdent "cg"
         c <- unqualifiedName
         pure (CG c)

setOption : Bool -> Rule REPLOpt
setOption set
    = do exactIdent "showimplicits"
         pure (ShowImplicits set)
  <|> do exactIdent "shownamespace"
         pure (ShowNamespace set)
  <|> do exactIdent "showtypes"
         pure (ShowTypes set)
  <|> if set then setVarOption else fatalError "Unrecognised option"

replCmd : List String -> Rule ()
replCmd [] = fail "Unrecognised command"
replCmd (c :: cs)
    = exactIdent c
  <|> replCmd cs

export
editCmd : Rule EditCmd
editCmd
    = do replCmd ["typeat"]
         line <- intLit
         col <- intLit
         n <- name
         pure (TypeAt (fromInteger line) (fromInteger col) n)
  <|> do replCmd ["cs"]
         line <- intLit
         col <- intLit
         n <- name
         pure (CaseSplit (fromInteger line) (fromInteger col) n)
  <|> do replCmd ["ac"]
         line <- intLit
         n <- name
         pure (AddClause (fromInteger line) n)
  <|> do replCmd ["ps", "proofsearch"]
         line <- intLit
         n <- name
         pure (ExprSearch (fromInteger line) n [] False)
  <|> do replCmd ["psall"]
         line <- intLit
         n <- name
         pure (ExprSearch (fromInteger line) n [] True)
  <|> do replCmd ["gd"]
         line <- intLit
         n <- name
         pure (GenerateDef (fromInteger line) n)
  <|> do replCmd ["ml", "makelemma"]
         line <- intLit
         n <- name
         pure (MakeLemma (fromInteger line) n)
  <|> do replCmd ["mc", "makecase"]
         line <- intLit
         n <- name
         pure (MakeCase (fromInteger line) n)
  <|> do replCmd ["mw", "makewith"]
         line <- intLit
         n <- name
         pure (MakeWith (fromInteger line) n)
  <|> fatalError "Unrecognised command"

export
command : Rule REPLCmd
command
    = do symbol ":"; replCmd ["t", "type"]
         tm <- expr EqOK "(interactive)" init
         pure (Check tm)
  <|> do symbol ":"; replCmd ["printdef"]
         n <- name
         pure (PrintDef n)
  <|> do symbol ":"; replCmd ["s", "search"]
         n <- name
         pure (ProofSearch n)
  <|> do symbol ":"; exactIdent "di"
         n <- name
         pure (DebugInfo n)
  <|> do symbol ":"; replCmd ["q", "quit", "exit"]
         pure Quit
  <|> do symbol ":"; exactIdent "set"
         opt <- setOption True
         pure (SetOpt opt)
  <|> do symbol ":"; exactIdent "unset"
         opt <- setOption False
         pure (SetOpt opt)
  <|> do symbol ":"; replCmd ["c", "compile"]
         n <- unqualifiedName
         tm <- expr EqOK "(interactive)" init
         pure (Compile tm n)
  <|> do symbol ":"; exactIdent "exec"
         tm <- expr EqOK "(interactive)" init
         pure (Exec tm)
  <|> do symbol ":"; replCmd ["r", "reload"]
         pure Reload
  <|> do symbol ":"; replCmd ["e", "edit"]
         pure Edit
  <|> do symbol ":"; replCmd ["miss", "missing"]
         n <- name
         pure (Missing n)
  <|> do symbol ":"; keyword "total"
         n <- name
         pure (Total n)
  <|> do symbol ":"; cmd <- editCmd
         pure (Editing cmd)
  <|> do tm <- expr EqOK "(interactive)" init
         pure (Eval tm)
