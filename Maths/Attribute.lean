import Lean.Elab.Command

open Lean Elab

initialize tagExt : SimplePersistentEnvExtension Unit Bool ←
  registerSimplePersistentEnvExtension {
    addImportedFn as := False
    addEntryFn _ _ := True
  }

def markInitialised {m : Type → Type} [MonadEnv m] : m Unit :=
  modifyEnv (tagExt.addEntry · ())

def isInitialised {m : Type → Type} [MonadEnv m] [Monad m] : m Bool := do
  let env ← getEnv
  pure $ tagExt.getState env
