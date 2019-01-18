module Compiler.Scheme.Erlang

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Scheme.ErlangCommon
import Compiler.Scheme.FileUtils

import Core.Context
import Core.Directory
import Core.Name
import Core.TT

import Data.List
import Data.Vect
import System
import System.Info

%default covering

record Opts where
  constructor MkOpts
  moduleName : String


findErlangCompiler : IO String
findErlangCompiler = pure "/usr/bin/env erlc"

findEscript : IO String
findEscript = pure "/usr/bin/env escript"

mutual
  racketPrim : SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  racketPrim vs CCall [ret, fn, args, world]
      = throw (InternalError ("Can't compile C FFI calls to Erlang yet"))
  racketPrim vs prim args 
      = schExtCommon racketPrim vs prim args

compileToErlang : Opts -> Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot ()
compileToErlang (MkOpts moduleName) c tm outfile
    = do ns <- findUsedNames tm
         defs <- get Ctxt
         compdefs <- traverse (getScheme racketPrim defs) ns
         let code = concat compdefs
         main <- schExp racketPrim [] !(compileExp tm)
         support <- readDataFile "erlang/support.erl"
         let scm = header ++ support ++ code ++ "main(Args) -> " ++ main ++ ".\n"
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()
  where
    header : String
    header = "-module('" ++ moduleName ++ "').\n" ++
      "-export([main/1]).\n" ++
      "\n"


erlangModuleName : String -> Maybe String
erlangModuleName path = rootname !(basename path)

-- TODO: Add error handling
generateErl : Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
generateErl c tm outfile = do
  let Just modName = erlangModuleName outfile
    | throw (InternalError ("Invalid module name: " ++ outfile))
  let opts = MkOpts modName
  compileToErlang opts c tm outfile
  pure (Just outfile)

-- TODO: Add error handling
-- TODO: Add options to `erlc`
generateBeam : Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
generateBeam c tm outfile = do
  let Just modName = erlangModuleName outfile
    | throw (InternalError ("Invalid module name: " ++ outfile))
  let targetDir : String =
    case dirname outfile of
      Just path => path
      _ => "."
  tmpDir <- coreLift $ tmpName
  erlc <- coreLift findErlangCompiler
  coreLift $ system ("mkdir -p " ++ quoted tmpDir)
  let generatedFile = tmpDir ++ "/" ++ modName ++ ".erl"
  let opts = MkOpts modName
  compileToErlang opts c tm generatedFile
  coreLift $ system (erlc ++ " -W0 -o " ++ quoted targetDir ++ " " ++ quoted generatedFile)
  pure (Just outfile)

-- TODO: generateEscript : Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot (Maybe String)

-- TODO: Validate `outfile`
compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
compileExpr c tm outfile =
  case extension outfile of
    Just "erl" => generateErl c tm outfile
    Just "beam" => generateBeam c tm outfile
    _ => throw (InternalError ("Unknown file type: " ++ outfile))

-- TODO: Add error handling
executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core annot ()
executeExpr c tm
    = do escript <- coreLift $ findEscript
         tmp <- coreLift $ tmpName
         let generatedFile = tmp ++ ".erl"
         let opts = MkOpts "main"
         compileToErlang opts c tm generatedFile
         coreLift $ system (escript ++ " " ++ quoted generatedFile)
         pure ()

export
codegenErlang : Codegen annot
codegenErlang = MkCG compileExpr executeExpr
