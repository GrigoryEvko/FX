import Tests.Framework

/-!
# Runner — CLI argument plumbing for `fxi-tests`

The runtime harness lives in `Tests.Framework`; this module owns
the executable glue: argv parsing, `--help` / `--list`, output-
format selection, suite filtering.  Splitting it off keeps
`Framework.lean` import-only (it can be consumed by test files
without dragging in any CLI code) and makes the runner
independently testable.

## Surface area

  * `Action` — discriminated sum of what the binary was asked to do.
  * `parseArgs : List String → Except String Action` — deterministic
    left-to-right parse; unknown flags are errors.
  * `helpText` — shown for `--help` and on argument errors.
-/

namespace Tests.Runner

/-- What `main` should do after parsing argv. -/
inductive Action
  | help
  | list
  | run (runConfig : RunConfig)
  deriving Inhabited

/-- Human-readable usage message.  Included in the source as a
    raw string so the `--help` output and the docstring stay in
    sync. -/
def helpText : String :=
  "fxi-tests — runtime test suite\n" ++
  "\n" ++
  "Usage:\n" ++
  "  fxi-tests [flags]\n" ++
  "\n" ++
  "Flags:\n" ++
  "  --help, -h            Show this help and exit.\n" ++
  "  --list                List registered suite titles and exit.\n" ++
  "  --verbose, -v         Print a line for each passing check.\n" ++
  "  --suite NAME          Only run suites whose title contains NAME.\n" ++
  "                        May be given once; last wins.\n" ++
  "  --format FORMAT       One of: human (default), tap, json.\n" ++
  "  --format=FORMAT       Same, with equals sign.\n" ++
  "\n" ++
  "Exit code is 0 iff every suite passed and no suite crashed."

private def parseFormat (formatName : String) : Except String OutputFormat :=
  match formatName with
  | "human" => .ok .human
  | "tap"   => .ok .tap
  | "json"  => .ok .json
  | _       => .error s!"unknown --format value: {formatName} (want human|tap|json)"

/-- Parse argv into an `Action`.  Deterministic, no IO.  Single
    pass; unknown flags are errors so typos don't silently fall
    through.  Positional arguments are reserved for a future
    "run only these suite titles" feature and currently error. -/
def parseArgs : List String → Except String Action
  | [] => .ok (.run {})
  | args =>
    let rec go (runConfig : RunConfig) : List String → Except String Action
      | []                    => .ok (.run runConfig)
      | currentArg :: remaining =>
        match currentArg with
        | "--help" | "-h" => .ok .help
        | "--list"        => .ok .list
        | "--verbose" | "-v" =>
          go { runConfig with verbose := true } remaining
        | "--suite" =>
          match remaining with
          | [] => .error "--suite requires an argument"
          | suiteName :: tail => go { runConfig with filter := some suiteName } tail
        | "--format" =>
          match remaining with
          | [] => .error "--format requires an argument"
          | formatName :: tail =>
            match parseFormat formatName with
            | .ok fmt         => go { runConfig with format := fmt } tail
            | .error parseErr => .error parseErr
        | other =>
          if other.startsWith "--format=" then
            let formatName := (other.drop "--format=".length).toString
            match parseFormat formatName with
            | .ok fmt         => go { runConfig with format := fmt } remaining
            | .error parseErr => .error parseErr
          else if other.startsWith "--suite=" then
            let suiteName := (other.drop "--suite=".length).toString
            go { runConfig with filter := some suiteName } remaining
          else
            .error s!"unknown argument: {other}"
    go {} args

end Tests.Runner
