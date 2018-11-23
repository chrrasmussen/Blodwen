module Compiler.Scheme.Erlang

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Scheme.ErlangCommon

import Core.Context
import Core.Directory
import Core.Name
import Core.TT

import Data.List
import Data.Vect
import System
import System.Info

%default covering

findErlangCompiler : IO String
findErlangCompiler = pure "/usr/bin/env erlc"

findEscript : IO String
findEscript = pure "/usr/bin/env escript"

schHeader : String
schHeader = "" -- TODO: "-module(main).\n-export([main/1]).\n\n"

schFooter : String
schFooter = ""

mutual
  racketPrim : SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  racketPrim vs CCall [ret, fn, args, world]
      = throw (InternalError ("Can't compile C FFI calls to Erlang yet"))
  racketPrim vs prim args 
      = schExtCommon racketPrim vs prim args

-- TODO: Implement
compileToErlang : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core annot ()
compileToErlang c tm outfile
    = do ns <- findUsedNames tm
         --coreLift (printLn ns) -- TODO: Remove!
         defs <- get Ctxt
         compdefs <- traverse (getScheme racketPrim defs) ns
         let code = concat compdefs
         --coreLift (printLn !(compileExp tm)) -- TODO: Remove!
         --pure ()
         main <- schExp racketPrim [] !(compileExp tm)
         support <- readDataFile "erlang/support.erl"
         let scm = schHeader ++ support ++ code ++ "main(Args) -> " ++ main ++ ".\n" ++ schFooter
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
compileExpr c tm outfile = pure Nothing
    -- = do tmp <- coreLift $ tmpName
    --      let outn = tmp ++ ".erl"
    --      compileToRKT c tm outn
    --      raco <- coreLift findRacoExe
    --      ok <- coreLift $ system (raco ++ " -o " ++ outfile ++ " " ++ outn)
    --      if ok == 0
    --         then pure (Just outfile)
    --         else pure Nothing

executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core annot ()
executeExpr c tm
    = do erlc <- coreLift $ findErlangCompiler
         escript <- coreLift $ findEscript
         tmpDir <- coreLift $ tmpName
         coreLift $ system ("mkdir -p " ++ tmpDir)
         let generatedFile = tmpDir ++ "/main.erl"
         let compiledFile = tmpDir ++ "/main.beam"
         compileToErlang c tm generatedFile
         coreLift $ system (erlc ++ " -W0 -o " ++ tmpDir ++ " " ++ generatedFile)
         coreLift $ system (escript ++ " " ++ compiledFile)
         pure ()

export
codegenErlang : Codegen annot
codegenErlang = MkCG compileExpr executeExpr

