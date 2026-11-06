import Duper.Tactic
import Auto.Tactic

open Lean Auto

def Auto.duperRaw (ni : NativeInterface Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← ni.valids.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuper lemmas.toList [] 0

def Auto.duperPort (ni : NativeInterface Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← ni.valids.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuperPortfolioMode
    (lemmas.toList.map (fun ⟨e₁, e₂, ns, b⟩ => ⟨e₁, e₂, ns, b, .none⟩)) []
    .none ⟨true, .none, .none, .none, .none, .none⟩ .none
