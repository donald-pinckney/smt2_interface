import Init.System.IO

-- structure z3_instance : Type :=
--   (process : IO.Process.Child { stdin := IO.Process.Stdio.piped, stdout := IO.Process.Stdio.piped, stderr := IO.Process.Stdio.inherit } )

-- def z3_instance.start : IO z3_instance := do
--   z3_instance.mk <$> IO.Process.spawn {
--       cmd := "z3",
--       args := #["-smt2", "-in"],
--       stdin := IO.Process.Stdio.piped,
--       stdout := IO.Process.Stdio.piped
--   }

-- def z3_instance.stop (z3 : z3_instance) : IO Unit := do
--   let (_stdin, proc) ← z3.process.takeStdin
--   IO.println "waiting"
--   let _exit_code ← proc.wait
--   return ()

def z3_instance.raw (cmd : String) : IO String :=
  -- let z3_stdin := z3.process.stdin
  -- let z3_stdout := z3.process.stdout
  do 
    let z3_proc ← IO.Process.spawn {
      cmd := "z3",
      args := #["-smt2", "-in"],
      stdin := IO.Process.Stdio.piped,
      stdout := IO.Process.Stdio.piped
    }

    -- IO.println $ "putting str: " ++ cmd
    IO.FS.Handle.putStrLn z3_proc.stdin cmd
    IO.FS.Handle.flush z3_proc.stdin

    let (_stdin, z3_proc) ← z3_proc.takeStdin

    -- IO.println "reading str"
    let res ← IO.FS.Handle.readToEnd z3_proc.stdout
    -- let res ← IO.FS.Handle.getLine z3.process.stdout
    -- IO.println $ "read str: " ++ res

    let _exit_code ← z3_proc.wait

    -- IO.println "waiting"
    -- let exit_code ← z3.process.wait
    -- IO.println $ "done with exit code: " ++ toString exit_code

    return res
