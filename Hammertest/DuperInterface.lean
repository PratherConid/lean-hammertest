import Auto.Tactic
import Duper.Tactic

open Lean Auto

def Auto.duperRaw (lemmas : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨proof, ty, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  runDuper lemmas.data 0

def Auto.duperPort (lemmas : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨proof, ty, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  runDuperPortfolioMode lemmas.data .none ⟨true, .none, .none, .none, .none, .none⟩ .none
