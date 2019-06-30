module Compiler.Erlang.Erlang

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Erlang.Common
import Compiler.Erlang.FileUtils

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT

import Data.CMap
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

data ExportMainFunc = IncludeMain | ExcludeMain

header : String -> ExportMainFunc -> String
header moduleName exportMainFunc = do
  let exportDirective =
    case exportMainFunc of
      IncludeMain => "-export([main/1]).\n"
      ExcludeMain => ""
  "-module('" ++ moduleName ++ "').\n" ++
    -- "-mode(compile).\n" ++ -- TODO: Make mode into a flag
    "-compile([nowarn_unused_function, nowarn_unused_vars]).\n" ++
    exportDirective ++
    "\n"

compileToErlangExecutable : Opts -> Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot ()
compileToErlangExecutable (MkOpts moduleName) c tm outfile = do
    ds <- getDirectives Erlang
    (names, tags) <- findUsedNames tm
    defs <- get Ctxt
    compdefs <- traverse (genErlang defs) names
    let code = concat compdefs
    main <- genExp 0 [] !(compileExp tags tm)
    support <- readDataFile "erlang/support.erl"
    let scm = header moduleName IncludeMain ++ unlines ds ++ support ++ code ++ "main(Args) -> " ++ mainInit ++ ", " ++ main ++ ".\n"
    Right () <- coreLift $ writeFile outfile scm
      | Left err => throw (FileErr outfile err)
    coreLift $ chmod outfile 0o755
    pure ()
  where
    mainInit : String
    mainInit = "persistent_term:put('$idris_rts_args', Args), io:setopts([{encoding, unicode}])"

compileToErlangLibrary : Opts -> Ref Ctxt Defs -> ClosedTerm -> (libEntrypoint : String) -> (outfile : String) -> Core annot ()
compileToErlangLibrary (MkOpts moduleName) c tm libEntrypoint outfile = do
    ds <- getDirectives Erlang
    (names, tags) <- findUsedNames tm
    defs <- get Ctxt
    let exportsFuncName = NS (currentNS defs) (UN libEntrypoint)
    compdefs <- traverse (genErlang defs) (filter (/= exportsFuncName) names)
    let code = concat compdefs
    (exportDirectives, exportFuncs) <- genErlangExports defs exportsFuncName
    -- NOTE: The main function is not used, but (for some reason) it is referenced by the generated code.
    main <- genErlang defs exportsFuncName
    support <- readDataFile "erlang/support.erl"
    let scm = header moduleName ExcludeMain ++ exportDirectives ++ unlines ds ++ support ++ code ++ main ++ exportFuncs ++ "\n"
    Right () <- coreLift $ writeFile outfile scm
      | Left err => throw (FileErr outfile err)
    coreLift $ chmod outfile 0o755
    pure ()

compileToErlang : Opts -> Ref Ctxt Defs -> ClosedTerm -> (libEntrypoint : Maybe String) -> (outfile : String) -> Core annot ()
compileToErlang opts c tm libEntrypoint outfile =
  case libEntrypoint of
    Just entrypoint => compileToErlangLibrary opts c tm entrypoint outfile
    Nothing => compileToErlangExecutable opts c tm outfile

erlangModuleName : String -> Maybe String
erlangModuleName path = rootname !(basename path)

-- TODO: Add error handling
generateErl : Ref Ctxt Defs -> ClosedTerm -> (libEntrypoint : Maybe String) -> (outfile : String) -> Core annot (Maybe String)
generateErl c tm libEntrypoint outfile = do
  let Just modName = erlangModuleName outfile
    | throw (InternalError ("Invalid module name: " ++ outfile))
  let opts = MkOpts modName
  compileToErlang opts c tm libEntrypoint outfile
  pure (Just outfile)

-- TODO: Add error handling
-- TODO: Add options to `erlc`
generateBeam : Ref Ctxt Defs -> ClosedTerm -> (libEntrypoint : Maybe String) -> (outfile : String) -> Core annot (Maybe String)
generateBeam c tm libEntrypoint outfile = do
  let Just modName = erlangModuleName outfile
    | throw (InternalError ("Invalid module name: " ++ outfile))
  let targetDir : String =
    case dirname outfile of
      Just path => path
      _ => "."
  erlc <- coreLift findErlangCompiler
  tmpDir <- coreLift $ tmpName
  coreLift $ system ("mkdir -p " ++ quoted tmpDir)
  let generatedFile = tmpDir ++ "/" ++ modName ++ ".erl"
  let opts = MkOpts modName
  compileToErlang opts c tm libEntrypoint generatedFile
  coreLift $ system (erlc ++ " -W0 -o " ++ quoted targetDir ++ " " ++ quoted generatedFile)
  pure (Just outfile)

-- TODO: generateEscript : Ref Ctxt Defs -> ClosedTerm -> (outfile : String) -> Core annot (Maybe String)

-- TODO: Validate `outfile`
compileExpr : Ref Ctxt Defs -> ClosedTerm -> (libEntrypoint : Maybe String) -> (outfile : String) -> Core annot (Maybe String)
compileExpr c tm libEntrypoint outfile =
  case extension outfile of
    Just "erl" => generateErl c tm libEntrypoint outfile
    Just "beam" => generateBeam c tm libEntrypoint outfile
    _ => throw (InternalError ("Unknown file type: " ++ outfile))

-- TODO: Add error handling
executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core annot ()
executeExpr c tm = do
  erlc <- coreLift findErlangCompiler
  escript <- coreLift $ findEscript
  tmpDir <- coreLift $ tmpName
  coreLift $ system ("mkdir -p " ++ quoted tmpDir)
  let generatedFile = tmpDir ++ "/main.erl"
  let compiledFile = tmpDir ++ "/main.beam"
  let opts = MkOpts "main"
  compileToErlang opts c tm Nothing generatedFile
  coreLift $ system (erlc ++ " -W0 -o " ++ quoted tmpDir ++ " " ++ quoted generatedFile)
  coreLift $ system (escript ++ " " ++ quoted compiledFile)
  pure ()

export
codegenErlang : Codegen annot
codegenErlang = MkCG compileExpr executeExpr

