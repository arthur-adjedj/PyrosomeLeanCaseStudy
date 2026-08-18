import Lean.PrettyPrinter.Delaborator.Basic
import Gemel
import Mathlib.Data.Quot
import Batteries.Tactic.GeneralizeProofs
set_option inductive.autoPromoteIndices false
-- TODO better syntax for match extensions
-- TODO better handling of aux declarations in `mod def`
set_option linter.auxLemma false
namespace Base

inductive Tag where
  | val
  | dummy --to avoid eta-for-unit
open Tag

inductive Ty where

def Tag.Data : Tag → Type
  | val => Ty
  | dummy => Unit

abbrev Ctx := List Ty

-- Pyrosome morally uses a mutual inductive type which separates values from expressions. LeanALaCarte does not yet handle mutual type/defs, so we bundle values and exprs in one type, with a tag to separate the two
inductive Expr : Ctx → (t : Tag) → t.Data → Type where
  | var {Γ A} (n : Fin Γ.length) (h : Γ[n] = A) : Expr Γ val A

def Expr.zero : Expr (A::Γ) val A := var 0 rfl

abbrev Ren (Γ Δ : Ctx) := {f : Fin Δ.length → Fin Γ.length // ∀ n, Δ[n] = Γ[f n]}

def Ren.lift' (r : Ren Γ Δ) : Fin (A::Δ).length → Fin (A::Γ).length
    | 0 => ⟨0,Nat.zero_lt_succ _⟩
    | ⟨n+1,h⟩ => (r.val ⟨n,Nat.lt_of_succ_lt_succ h⟩).succ

def Ren.lift (r : Ren Γ Δ) : Ren (A::Γ) (A::Δ) where
  val := r.lift'
  property := fun
    | 0 => rfl
    | ⟨n+1,h⟩ => r.2 ⟨n,Nat.lt_of_succ_lt_succ h⟩

def Ren.wk : Ren (A::Γ) Γ where
  val := Fin.succ
  property _ := rfl

def Expr.ren (r : Ren Γ Δ) : Expr Δ t A →  Expr Γ t A
  | .var n h₁ => .var (r.val n) (by rw [←h₁];symm; exact r.2 n)

def Expr.lift : Expr Γ t A → Expr (B::Γ) t A := Expr.ren Ren.wk

abbrev Sub (Γ Δ : Ctx) := (n : Fin Δ.length) → Expr Γ val Δ[n]

def Sub.id : Sub Γ Γ := fun n => .var n rfl

def Sub.wk (σ : Sub Γ Δ) : Sub (A::Γ) Δ :=
  fun n => (σ n).lift

def Sub.snoc (σ : Sub Γ Δ) (t : Expr Γ val A) : Sub Γ (A::Δ)
  | 0 => t
  | ⟨n+1,h⟩ => σ ⟨n,Nat.lt_of_succ_lt_succ h⟩

def Sub.lift (σ : Sub Γ Δ) : Sub (A::Γ) (A::Δ)
  | 0 => Expr.zero
  | ⟨n+1,h⟩ => σ ⟨n,Nat.lt_of_succ_lt_succ h⟩ |>.lift

@[simp]
theorem Sub.lift_succ (σ : Sub Γ Δ) : σ.lift (A := A) n.succ = (σ n).lift := rfl

def Expr.subst (σ : Sub Γ Δ) : Expr Δ t A → Expr Γ t A
  | .var n h => h ▸ σ n

inductive Equiv : Expr t Γ A → Expr t Γ A → Prop where
  | refl:  Equiv e e
  | symm : Equiv e₁ e₂ → Equiv e₂ e₁
  | trans : Equiv e₁ e₂ → Equiv e₂ e₃ → Equiv e₁ e₃

theorem Equiv.equiv : Equivalence (@Equiv t Γ A) where
  refl _ := .refl
  symm e := e.symm
  trans e₁ e₂ := e₁.trans e₂

instance Equiv.setoid: Setoid (Expr t Γ A) where
  r := Equiv
  iseqv := Equiv.equiv

end Base

modular STLC

namespace STLC
  mod inductive Tag extends Base.Tag where
    | exp
  open Tag

  mod inductive Ty extends Base.Ty where
    | arr (A B : Ty)

  @[reducible]
  mod def Tag.Data extends Base.Tag.Data where
    extend match_1 with
      | .exp => Ty

  @[reducible]
  mod def Ctx extends Base.Ctx

  mod def Expr._proof_1 extends Base.Expr._proof_1

  mod inductive Expr extends Base.Expr where
    | ret : Expr Γ val A → Expr Γ exp A
    | lam : Expr (A::Γ) exp B → Expr Γ val (.arr A B)
    | app : Expr Γ exp  (.arr A B) → Expr Γ exp  A → Expr Γ exp B

  mod def Expr.zero._proof_1 extends Base.Expr.zero._proof_1
  mod def Expr.zero._proof_2 extends Base.Expr.zero._proof_2
  mod def Expr.zero extends Base.Expr.zero

  @[reducible]
  mod def Ren extends Base.Ren
  mod def Ren.lift' extends Base.Ren.lift'
  -- TODO fix `mod def` elab s.t it accepts decls for which auxiliary decls appear in their type
  mod def Ren.lift._proof_1 extends Base.Ren.lift._proof_1
  mod def Ren.lift._proof_3 extends Base.Ren.lift._proof_3
  mod def Ren.lift extends Base.Ren.lift
  mod def Ren.wk extends Base.Ren.wk

  mod def Expr.ren._proof_1 extends Base.Expr.ren._proof_1 where
  mod def Expr.ren extends Base.Expr.ren where
    extend match_1 with
    | _, _, .ret v => .ret (Expr.ren r v)
    | _, _, .lam e => .lam (Expr.ren r.lift e)
    | _, _, .app f t => .app (Expr.ren r f) (Expr.ren r t)

  mod def Expr.lift extends Base.Expr.lift

  @[implicit_reducible]
  mod def Sub extends Base.Sub
  mod def Sub.id extends Base.Sub.id
  mod def Sub.wk extends Base.Sub.wk
  mod def Sub.snoc extends Base.Sub.snoc

  mod def Sub.lift extends Base.Sub.lift
  @[simp]
  mod def Sub.lift_succ extends Base.Sub.lift_succ

  mod def Expr.subst extends Base.Expr.subst where
    extend match_1 with
      | _, _, .ret v => .ret (Expr.subst σ v)
      | _, _, .lam f => .lam (Expr.subst σ.lift f)
      | _, _, .app f t => .app (Expr.subst σ f) (Expr.subst σ t)

  mod inductive Equiv extends Base.Equiv where
    | ret : Equiv v₁ v₂ → Equiv (.ret v₁) (.ret v₂)
    | lam : Equiv f₁ f₂ → Equiv (.lam f₁) (.lam f₂)
    | app : Equiv f₁ f₂ → Equiv t₁ t₂ → Equiv (.app f₁ t₁) (.app f₂ t₂)
    | beta : Equiv (.app (.ret (.lam e)) (.ret v)) (e.subst (Sub.id.snoc v))

  mod def Equiv.equiv extends Base.Equiv.equiv
  mod def Equiv.setoid extends Base.Equiv.setoid
end STLC
modular end STLC

modular STLCFix
  namespace STLCFix
  open STLC.Tag
  mod inductive Ty extends STLC.Ty where

  mod def Tag.Data extends STLC.Tag.Data where

  @[reducible]
  mod def Ctx extends STLC.Ctx

  mod def Expr._proof_1 extends STLC.Expr._proof_1

  mod inductive Expr extends STLC.Expr where
    | fix : Expr (A::(.arr A B)::Γ) exp B → Expr Γ val (.arr A B)

  mod def Expr.zero._proof_1 extends STLC.Expr.zero._proof_1
  mod def Expr.zero._proof_2 extends STLC.Expr.zero._proof_2
  mod def Expr.zero extends STLC.Expr.zero

  mod def Ren extends STLC.Ren
  mod def Ren.lift' extends STLC.Ren.lift'
  -- TODO fix `mod def` elab s.t it accepts decls for which auxiliary decls appear in their type
  mod def Ren.lift._proof_1 extends STLC.Ren.lift._proof_1
  mod def Ren.lift._proof_3 extends STLC.Ren.lift._proof_3
  mod def Ren.lift extends STLC.Ren.lift
  mod def Ren.wk extends STLC.Ren.wk
  mod def Expr.ren._proof_1 extends STLC.Expr.ren._proof_1
  mod def Expr.ren extends STLC.Expr.ren where
    extend match_4 with
      | _, _, .fix e => .fix (Expr.ren r.lift.lift e)

  mod def Expr.lift extends STLC.Expr.lift

  mod def Sub extends STLC.Sub
  mod def Sub.id extends STLC.Sub.id
  mod def Sub.wk extends STLC.Sub.wk
  mod def Sub.snoc extends STLC.Sub.snoc
  mod def Sub.lift extends STLC.Sub.lift

  mod def Expr.subst extends STLC.Expr.subst where
    extend match_4 with
      | _, _, .fix e => .fix (Expr.subst σ.lift.lift e)

  mod inductive Equiv extends STLC.Equiv where
    | fix : Equiv e e' → Equiv (.fix e) (.fix e')
    | fix_red : Equiv (.app (.ret (.fix e)) (.ret v)) (e.subst (Sub.id |>.snoc (.fix e) |>.snoc v))
end STLCFix
modular end STLCFix

modular STLCBool
  namespace STLCBool
  open STLC.Tag
  mod inductive Ty extends STLC.Ty where
    | bool

  mod def Tag.Data extends STLC.Tag.Data where

  @[reducible]
  mod def Ctx extends STLC.Ctx

  mod def Expr._proof_1 extends STLC.Expr._proof_1

  mod inductive Expr extends STLC.Expr where
    | true : Expr Γ val .bool
    | false : Expr Γ val .bool
    | ite : Expr Γ val .bool → Expr Γ exp A → Expr Γ exp A → Expr Γ exp A

  mod def Expr.zero._proof_1 extends STLC.Expr.zero._proof_1
  mod def Expr.zero._proof_2 extends STLC.Expr.zero._proof_2
  mod def Expr.zero extends STLC.Expr.zero

  mod def Ren extends STLC.Ren
  mod def Ren.lift' extends STLC.Ren.lift'
  -- TODO fix `mod def` elab s.t it accepts decls for which auxiliary decls appear in their type
  mod def Ren.lift._proof_1 extends STLC.Ren.lift._proof_1
  mod def Ren.lift._proof_3 extends STLC.Ren.lift._proof_3
  mod def Ren.lift extends STLC.Ren.lift
  mod def Ren.wk extends STLC.Ren.wk
  mod def Expr.ren._proof_1 extends STLC.Expr.ren._proof_1
  mod def Expr.ren extends STLC.Expr.ren where
    extend match_4 with
      | _, _, .true => .true
      | _, _, .false => .false
      | _, _, .ite b e₁ e₂ => .ite (Expr.ren r b) (Expr.ren r e₁) (Expr.ren r e₂)

  mod def Expr.lift extends STLC.Expr.lift

  mod def Sub extends STLC.Sub
  mod def Sub.id extends STLC.Sub.id
  mod def Sub.wk extends STLC.Sub.wk
  mod def Sub.snoc extends STLC.Sub.snoc
  mod def Sub.lift extends STLC.Sub.lift

  mod def Expr.subst extends STLC.Expr.subst where
    extend match_4 with
      | _, _, .true => .true
      | _, _, .false => .false
      | _, _, .ite b e₁ e₂ => .ite (Expr.subst σ b) (Expr.subst σ e₁) (Expr.subst σ e₂)

  mod inductive Equiv extends STLC.Equiv where
    | ite_true : Equiv (.ite .true e₁ e₂) e₁
    | ite_false : Equiv (.ite .false e₁ e₂) e₂
    | ite : Equiv b b' → Equiv e₁ e₁' → Equiv e₂ e₂' → Equiv (.ite b e₁ e₂) (.ite b' e₁' e₂')

end STLCBool
modular end STLCBool

modular STLCFixBool
  namespace STLCFixBool
  open STLC.Tag

  mod inductive Ty extends STLCFix.Ty, STLCBool.Ty where
    | bool

  mod def Tag.Data extends STLCFix.Tag.Data, STLCBool.Tag.Data where

  @[reducible]
  mod def Ctx extends STLCFix.Ctx, STLCBool.Ctx

  mod def Expr._proof_1 extends STLCFix.Expr._proof_1, STLCBool.Expr._proof_1

  mod inductive Expr extends STLCFix.Expr, STLCBool.Expr where
    | true : Expr Γ val .bool
    | false : Expr Γ val .bool
    | ite : Expr Γ val .bool → Expr Γ exp A → Expr Γ exp A → Expr Γ exp A

  mod def Expr.zero._proof_1 extends STLCFix.Expr.zero._proof_1, STLCBool.Expr.zero._proof_1
  mod def Expr.zero._proof_2 extends STLCFix.Expr.zero._proof_2, STLCBool.Expr.zero._proof_2
  mod def Expr.zero extends STLCFix.Expr.zero, STLCBool.Expr.zero

  mod def Ren extends STLCFix.Ren, STLCBool.Ren
  -- TODO the two ⟨n+1, h⟩ branches are not merged correctly here. This is benign here since they're the exact same, but this should be fixed nonetheless for the general case.
  set_option match.ignoreUnusedAlts true
  mod def Ren.lift' extends STLCFix.Ren.lift', STLCBool.Ren.lift'
  -- TODO fix `mod def` elab s.t it accepts decls for which auxiliary decls appear in their type
  mod def Ren.lift._proof_1 extends STLCFix.Ren.lift._proof_1, STLCBool.Ren.lift._proof_1
  mod def Ren.lift._proof_3 extends STLCFix.Ren.lift._proof_3, STLCBool.Ren.lift._proof_3
  mod def Ren.lift extends STLCFix.Ren.lift, STLCBool.Ren.lift
  mod def Ren.wk extends STLCFix.Ren.wk, STLCBool.Ren.wk
  mod def Expr.ren._proof_1 extends STLCFix.Expr.ren._proof_1, STLCBool.Expr.ren._proof_1
  mod def Expr.ren extends STLCFix.Expr.ren, STLCBool.Expr.ren
  mod def Expr.lift extends STLCFix.Expr.lift, STLCBool.Expr.lift

  mod def Sub extends STLCFix.Sub, STLCBool.Sub
  mod def Sub.id extends STLCFix.Sub.id, STLCBool.Sub.id
  mod def Sub.wk extends STLCFix.Sub.wk, STLCBool.Sub.wk
  mod def Sub.snoc extends STLCFix.Sub.snoc, STLCBool.Sub.snoc
  mod def Sub.lift extends STLCFix.Sub.lift, STLCBool.Sub.lift

  mod def Expr.subst extends STLCFix.Expr.subst, STLCBool.Expr.subst

  mod inductive Equiv extends STLCFix.Equiv, STLCBool.Equiv

end STLCFixBool
modular end STLCFixBool

modular CPS
  namespace CPS

  mod inductive Tag extends Base.Tag where
    | exp
  open Tag

  inductive PreTy where
    | not (A : PreTy)
    | times (A B : PreTy)

  inductive PreTy.Equiv : PreTy → PreTy → Prop where
    | not_not : Equiv A.not.not A
    | not : Equiv A₁ A₂ → Equiv A₁.not A₂.not
    | times : Equiv A₁ A₂ → Equiv B₁ B₂ → Equiv (A₁.times B₁) (A₂.times B₂)
    | refl : Equiv A A
    | symm : Equiv A B → Equiv B A
    | trans : Equiv A B → Equiv B C → Equiv A C

  attribute [grind .] PreTy.Equiv.not_not PreTy.Equiv.not PreTy.Equiv.times PreTy.Equiv.refl PreTy.Equiv.symm

  attribute [grind =] Quotient.eq
-- #exit
  grind_pattern PreTy.Equiv.trans => PreTy.Equiv A B, PreTy.Equiv B C

  abbrev Ty := Quotient ⟨PreTy.Equiv,@PreTy.Equiv.refl, PreTy.Equiv.symm, @PreTy.Equiv.trans⟩

  add_mapping Base.Ty => Ty

  def Ty.not (A : Ty) : Ty := Quotient.liftOn A (fun A => ⟦ A.not ⟧ ) fun a b e => by
    induction e <;> grind -abstractProof

  @[simp]
  theorem Ty.not_not (A : Ty) : A.not.not = A := by
    apply Quotient.recOnSubsingleton A (motive := fun A => (Ty.not A).not = A)
    intro a
    rw [not, not, Quotient.liftOn_mk, Quotient.liftOn_mk, Quotient.eq]
    apply PreTy.Equiv.not_not

  def Ty.times (A B: Ty) : Ty := Quotient.liftOn₂ A B (fun A B => ⟦ A.times B ⟧ ) fun a₁ a₂ b₁ b₂ e₁ e₂ => by
    induction e₁ <;> induction e₂
    <;> simp only [propext Quotient.eq, implies_true, *] at *
    <;> grind -abstractProof [PreTy]

  @[reducible]
  mod def Tag.Data extends Base.Tag.Data where
    extend match_1 with
      | .exp => Unit

  @[reducible]
  mod def Ctx extends Base.Ctx

  mod def Expr._proof_1 extends Base.Expr._proof_1

  mod inductive Expr extends Base.Expr where
    | lam : Expr (A::Γ) exp () → Expr Γ val A.not
    | app : Expr Γ val A.not → Expr Γ val A → Expr Γ exp ()
    | and_intro : Expr Γ val A → Expr Γ val B → Expr Γ val (A.times B)
    | fst : Expr Γ val (A.times B) → Expr Γ val A
    | snd : Expr Γ val (Ty.times A B) → Expr Γ val B

  mod def Expr.zero._proof_1 extends Base.Expr.zero._proof_1
  mod def Expr.zero._proof_2 extends Base.Expr.zero._proof_2
  mod def Expr.zero extends Base.Expr.zero

  mod def Ren extends Base.Ren
  mod def Ren.lift' extends Base.Ren.lift'
  -- TODO fix `mod def` elab s.t it accepts decls for which auxiliary decls appear in their type
  mod def Ren.lift._proof_1 extends Base.Ren.lift._proof_1
  mod def Ren.lift._proof_3 extends Base.Ren.lift._proof_3
  mod def Ren.lift extends Base.Ren.lift
  attribute [implicit_reducible] Ren Ren.lift
  mod def Ren.wk extends Base.Ren.wk

  mod def Expr.ren._proof_1 extends Base.Expr.ren._proof_1 where
  mod def Expr.ren extends Base.Expr.ren where
    extend match_1 with
    | _, _, .lam e => .lam (Expr.ren r.lift e)
    | _, _, .app f t => .app (Expr.ren r f) (Expr.ren r t)
    | _, _, .and_intro fst snd => .and_intro (Expr.ren r fst) (Expr.ren r snd)
    | _, _, .fst p => .fst (Expr.ren r p)
    | _, _, .snd p => .snd (Expr.ren r p)

  mod def Expr.lift extends Base.Expr.lift
  @[implicit_reducible]
  mod def Sub extends Base.Sub

  mod def Sub.id extends Base.Sub.id
  mod def Sub.wk extends Base.Sub.wk
  mod def Sub.snoc extends Base.Sub.snoc
  mod def Sub.lift extends Base.Sub.lift

  mod def Expr.subst extends Base.Expr.subst where
    extend match_1 with
      | _, _, .lam f => .lam (Expr.subst σ.lift f)
      | _, _, .app f t => .app (Expr.subst σ f) (Expr.subst σ t)
      | _, _, .and_intro fst snd => .and_intro (Expr.subst σ fst) (Expr.subst σ snd)
      | _, _, .fst p => .fst (Expr.subst σ p)
      | _, _, .snd p => .snd (Expr.subst σ p)

  mod inductive Equiv extends Base.Equiv where
    | lam : Equiv f₁ f₂ → Equiv (.lam f₁) (.lam f₂)
    | app : Equiv f₁ f₂ → Equiv t₁ t₂ → Equiv (.app f₁ t₁) (.app f₂ t₂)
    | beta (e : Expr (A::Γ) .exp ()) (v : Expr Γ .val A): Equiv (.app (.lam e) v) (e.subst (Sub.id.snoc v))
    | eta {v : Expr Γ val (.not A)}: Equiv (.lam (.app v.lift .zero)) v
    | and_intro : Equiv fst₁ fst₂ → Equiv snd₁ snd₂ → Equiv (.and_intro fst₁ snd₁) (.and_intro fst₂ snd₂)
    | fst : Equiv p₁ p₂ → Equiv p₁.fst p₂.fst
    | snd : Equiv p₁ p₂ → Equiv p₁.snd p₂.snd
    | fst_beta : Equiv (.fst (.and_intro fst snd)) fst
    | snd_beta : Equiv (.snd (.and_intro fst snd)) snd
    | eta_and : Equiv p (.and_intro p.fst p.snd)

  mod def Equiv.equiv extends Base.Equiv.equiv
  mod def Equiv.setoid extends Base.Equiv.setoid

def Sub.and (σ : Sub Γ Δ) : Sub ((Ty.times A B)::Γ) (B::A::Δ)
  | 0 => Expr.zero.snd
  | 1 => Expr.zero.fst
  | ⟨n+2,h⟩ => (σ ⟨n,Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)⟩).lift

def Ren.comp (r₁ : Ren Γ Δ) (r₂ : Ren Δ Φ) : Ren Γ Φ where
  val := r₁.val ∘ r₂.val
  property n := r₂.property n |>.trans (r₁.property (r₂.val n))

theorem Ren.lift_comp_lift (r₁ : Ren Γ Δ) (r₂ : Ren Δ Φ) : (r₁.comp r₂).lift (A := A) = (r₁.lift.comp r₂.lift) := by
  simp [Ren]
  ext
  rename_i x
  obtain ⟨x,_⟩ := x
  cases x <;> rfl

theorem Expr.ren_of_ren_ren  {r₁ : Ren Γ Δ} {r₂ : Ren Δ Φ} (v : Expr Φ t A) : (v.ren r₂).ren r₁ = v.ren (r₁.comp r₂) := by
  induction v generalizing r₁ Γ Δ <;> simp [ren, Ren.lift_comp_lift, *]
  case var => rfl

theorem Expr.ren_lift_wk {r : Ren Γ Δ} : (r.lift.comp Ren.wk) = ((Ren.wk (A := B)).comp r) := by
  simp [Ren.comp, Ren.lift, Ren.wk]
  rfl

theorem Expr.lift_ren_lift {r : Ren Γ Δ} (v : Expr Δ t A): Expr.ren r.lift v.lift = (Expr.ren r v).lift (B := B) := by
  rw [Expr.lift, Expr.lift, Expr.ren_of_ren_ren, Expr.ren_of_ren_ren]
  rfl

def Sub.ren_comp (ρ : Ren Γ Δ) (σ : Sub Δ Φ) : Sub Γ Φ := fun n =>
  (σ n).ren ρ

def Sub.comp_ren (σ : Sub Γ Δ) (ρ : Ren Δ Φ) : Sub Γ Φ := fun n =>
  (ρ.2 n) ▸ σ (ρ.val n)

@[simp]
theorem Sub.snoc_comp_ren_wk (σ : Sub Γ Δ) : (σ.snoc t).comp_ren .wk = σ := rfl

def Sub.comp (σ₁ : Sub Γ Δ) (σ₂ : Sub Δ Φ) : Sub Γ Φ :=
  fun n => (σ₂ n).subst σ₁

@[simp]
theorem Sub.wk_snoc_zero (σ : Sub Γ Δ) : (σ.wk (A := A)).snoc Expr.zero = σ.lift := rfl

@[simp]
theorem Sub.lift_zero (σ : Sub Γ Δ) : σ.lift (A := A) ⟨0,h⟩ = Expr.zero := rfl

@[simp]
theorem Sub.snoc_zero (σ : Sub Γ Δ) : σ.snoc e 0 = e := rfl

@[simp]
theorem Sub.snoc_succ (σ : Sub Γ Δ) : σ.snoc e n.succ = σ n := rfl

@[simp]
theorem Sub.lift_succ (σ : Sub Γ Δ) : σ.lift (A := A) n.succ = (σ n).lift := rfl

theorem Sub.ren_comp_lift {r : Ren Γ Δ} {σ : Sub Δ Φ} : (σ.ren_comp r).lift (A := A) = σ.lift.ren_comp r.lift  := by
  funext x
  simp
  cases x using Fin.cases
  · rfl
  · simp [ren_comp, Expr.lift, Expr.ren_of_ren_ren]
    rfl

theorem Sub.comp_ren_lift {σ : Sub Γ Δ} {r : Ren Δ Φ} : (σ.comp_ren r).lift (A := A) = σ.lift.comp_ren r.lift  := by
  funext x
  simp
  cases x using Fin.cases
  · rfl
  · simp only [lift, Expr.lift, Fin.getElem_fin, comp_ren,
    List.length_cons]
    conv =>
      rhs
      arg 1
      whnf
    conv =>
      lhs
      whnf
    grind only [= Lean.Grind.toInt_fin, usr Subtype.property, usr Fin.val_succ]

theorem Sub.comp_comp_ren {σ : Sub Γ Δ} {τ : Sub Δ Φ} {r : Ren Φ Ξ} : σ.comp (τ.comp_ren r) = (σ.comp τ).comp_ren r := by
  funext x
  simp [Sub.comp, Sub.comp_ren]
  grind -abstractProof only [usr Subtype.property]

theorem Sub.comp_ren_comp_ren {σ : Sub Γ Δ} {r₁ : Ren Δ Φ} {r₂ : Ren Φ Ξ} : σ.comp_ren (r₁.comp r₂) = (σ.comp_ren r₁).comp_ren r₂ := by
  funext x
  simp [Ren.comp, Sub.comp_ren]
  grind -abstractProof only

theorem Sub.wk_of_lift_comp_ren_wk {σ : Sub Γ Δ} : (σ.lift.comp_ren Ren.wk) = σ.wk (A := A) := by
  funext ⟨x,_⟩
  rw [comp_ren, Sub.wk, Expr.lift, Ren.wk]
  simp only
  rw [Sub.lift_succ, Expr.lift]

theorem Sub.head (σ : Sub Γ Δ) : Expr.subst (σ.snoc t) Expr.zero = t := rfl
theorem Sub.tail (σ : Sub Γ Δ) : (σ.snoc t).comp Sub.id.wk = σ := rfl

theorem Sub.eta (σ : Sub Γ (A::Δ)) : (σ.comp Sub.id.wk).snoc (σ 0) = σ := by
  funext ⟨n,_⟩
  cases n <;> rfl

theorem Sub.Zshift' : Sub.id.wk.snoc Expr.zero = @Sub.id (A::Γ) := by
  funext ⟨n,_⟩
  cases n <;> rfl

theorem Sub.Zshift : Sub.id.lift = @Sub.id (A::Γ) := Zshift'

theorem Sub.idR (σ : Sub Γ Δ) : (σ.comp Sub.id) = σ := rfl

@[simp]
theorem Expr.subst_id : Expr.subst Sub.id t = t := by
  induction t <;> simp [Sub.Zshift, subst, *]
  case var h => cases h; rfl

@[simp]
theorem Sub.idL (σ : Sub Γ Δ) : Sub.comp Sub.id σ = σ := by
  funext n
  apply Expr.subst_id

theorem Expr.subst_ren (t : Expr Φ t A) (ρ : Ren Γ Δ) (σ : Sub Δ Φ) : (t.subst σ).ren ρ = t.subst (σ.ren_comp ρ) := by
  induction t generalizing ρ Γ Δ <;> simp [Sub.ren_comp, ren, subst, *]
  case var h => cases h; rfl
  case lam ih =>
    rw [Sub.ren_comp_lift]

@[simp]
theorem Ren.lift_succ (ρ : Ren Γ Δ) : (ρ.lift (A := A)).val n.succ = (ρ.val n).succ := rfl

theorem Expr.ren_subst (t : Expr Φ t A) (σ : Sub Γ Δ) (ρ : Ren  Δ Φ) : (t.ren ρ).subst σ = t.subst (Sub.comp_ren σ ρ) := by
  induction t generalizing σ Γ Δ <;> simp [Sub.comp_ren, ren, subst, *]
  case var h => cases h; rfl
  case lam ih =>
    have := ih σ.lift ρ.lift
    rw [← this, Sub.comp_ren_lift]
    assumption

theorem Sub.comp_ren_comp {σ : Sub Γ Δ} {r : Ren Δ Φ} {τ : Sub Φ Ξ} : σ.comp (τ.ren_comp r) = (σ.comp_ren r).comp τ := by
  funext x
  simp [Sub.comp, Sub.ren_comp, Expr.ren_subst]

theorem Expr.lift_subst_lift (t : Expr Δ t B) (σ : Sub Γ Δ) :
(t.lift (A := B)).subst σ.lift = (t.subst σ).lift (B := A) := by
  induction t <;> simp [Expr.lift, Expr.ren, Expr.subst, *] at *
  case var h => cases h; rfl
  case lam ih =>
    rw [Expr.subst_ren, ← Sub.ren_comp_lift, Expr.ren_subst, ← Sub.comp_ren_lift]
    rfl
  case app ih₁ ih₂ | and_intro ih₁ ih₂ => exact ⟨ih₁ _, ih₂ _⟩

@[simp]
theorem Sub.comp_lift {σ : Sub Γ Δ} {τ : Sub Δ Φ} : Sub.comp σ.lift τ.lift = (Sub.comp σ τ).lift (A := A) := by
  funext x
  cases x using Fin.cases
  case zero => rfl
  case succ n =>
    simp [Sub.comp, Expr.lift, Expr.ren_subst , Expr.subst_ren]
    rfl

theorem Expr.subst_subst  {σ₁ : Sub Γ Δ} {σ₂ : Sub Δ Φ} (v : Expr Φ t A) : (v.subst σ₂).subst σ₁ = v.subst (σ₁.comp σ₂) := by
  induction v generalizing σ₁ Γ Δ <;> simp only [subst, Fin.getElem_fin, Sub.comp, *]
  case var h =>
    cases h
    rfl
  case lam A Φ t ih =>
    rw [Sub.comp_lift]

theorem Sub.comp_comp {σ : Sub Γ Δ} {τ : Sub Δ Φ} {φ : Sub Φ Ξ} : σ.comp (τ.comp φ) = (σ.comp τ).comp φ := by
  funext x
  simp [Sub.comp, Expr.subst_subst]

theorem Expr.cast_val {h : Γ[n] = A}(e : A = B) : cast (congrArg _ e) (Expr.var n h) = Expr.var n (cast (congrArg _ e) h) := by cases e; rfl
theorem Expr.cast_val' {h : Γ[n] = A} (e : A = B) : e ▸ (Expr.var n h) = Expr.var n (e ▸ h) := by cases e; rfl

theorem Equiv.ren {r : Ren Γ Δ} (e₁ e₂ : Expr Δ t A) : Equiv e₁ e₂ → Equiv (e₁.ren r) (e₂.ren r) := by
  intro h
  induction h generalizing Γ
  case refl => exact .refl
  case symm ih => exact .symm ih
  case trans ih₁ ih₂ => exact .trans ih₁ ih₂
  case lam ih => exact Equiv.lam ih
  case app ih₁ ih₂ => exact Equiv.app ih₁ ih₂
  case and_intro ih₁ ih₂ => exact Equiv.and_intro ih₁ ih₂
  case eta_and => exact .eta_and
  case fst ih => exact .fst ih
  case snd ih => exact .snd ih
  case fst_beta => exact .fst_beta
  case snd_beta => exact .snd_beta
  case eta v =>
    simp [Expr.ren, Expr.zero, Expr.lift_ren_lift]
    exact Equiv.eta (v := (Expr.ren r v))
  case beta =>
    simp [Expr.ren]
    apply Equiv.trans
    · apply Equiv.beta
    · rename_i e v
      have : (e.ren r.lift).subst (Sub.id.snoc (Expr.ren r v)) = (e.subst (Sub.id.snoc v)).ren r := by
        simp [Expr.subst_ren, Expr.ren_subst]
        congr 1
        funext x
        cases x using Fin.cases
        case zero => rfl
        case succ x h =>
          simp [Sub.comp_ren, Sub.ren_comp, Sub.id, Expr.ren]
          apply Expr.cast_val'
      rw [this]
      apply Equiv.refl

theorem Equiv.subst {σ : Sub Γ Δ} {e₁ e₂ : Expr Δ t A}  : Equiv e₁ e₂ → Equiv (e₁.subst σ) (e₂.subst σ) := by
  intro h
  induction h generalizing Γ
  case refl => exact .refl
  case symm ih => exact .symm ih
  case trans ih₁ ih₂ => exact .trans ih₁ ih₂
  case lam ih => exact Equiv.lam ih
  case app ih₁ ih₂ => exact Equiv.app ih₁ ih₂
  case and_intro ih₁ ih₂ => exact Equiv.and_intro ih₁ ih₂
  case eta_and => exact .eta_and
  case fst ih => exact .fst ih
  case snd ih => exact .snd ih
  case fst_beta => exact .fst_beta
  case snd_beta => exact .snd_beta
  case eta v =>
    simp [Expr.subst, Expr.zero, Expr.lift_subst_lift]
    exact Equiv.eta (v := (Expr.subst σ v))
  case beta e v =>
    apply Equiv.trans
    · apply Equiv.beta
    · have : (Expr.subst (Sub.id.snoc (Expr.subst σ v)) (Expr.subst σ.lift e)) = (Expr.subst σ (Expr.subst (Sub.id.snoc v) e)) := by
        simp [Expr.subst_subst]
        congr 1
        funext n
        cases n using Fin.cases
        · rfl
        · simp [Sub.comp, Sub.id, Expr.subst, Expr.lift, Expr.ren_subst]
      rw [this]
      apply Equiv.refl
modular end _root_.CPS

theorem Equiv.cast  (h₁ : Expr Γ t A = Expr Γ t B) (h₂ : A = B) (e₁ e₂ : Expr Γ t A) : Equiv e₁ e₂ →
  Equiv (cast h₁ e₁) (cast h₁ e₂) := by
  cases h₂
  cases h₁
  exact id

theorem Expr.cast_ren {A B : t.Data} {ρ : Ren Δ Γ} (h : A = B) (hΓ : Γ = Γ') (hΔ : Δ = Δ') (h₁ : Expr Γ' t A = Expr Γ t B) (h₂ : Expr Δ t A = Expr Δ' t B)  (e : Expr Γ' t A) : (cast h₁ e).ren ρ = cast (congrArg (Expr · t B) hΔ.symm) (cast h₂ ((cast (congrArg (Expr · t A) hΓ.symm) e).ren ρ)) := by
  cases h
  cases hΔ
  cases hΓ
  rfl

theorem Expr.cast_subst {A B : t.Data} {σ : Sub Δ Γ} (h : A = B) (hΓ : Γ' = Γ) (hΔ : Δ' = Δ) (e : Expr Γ' t A) : (cast (congrArg₂ (Expr · t ·) hΓ h) e).subst σ = cast (congrArg (Expr Δ t) h) ((cast (congrArg (Expr · t A) hΓ) e).subst σ) := by
  subst h hΔ hΓ
  rfl

theorem Expr.cast_zero (h : A = B) (h₁ : Expr (A::Γ) .val A = Expr (B::Γ) .val B): (cast h₁ Expr.zero) = Expr.zero := by
  cases h
  rfl

theorem Expr.cast_lam (h : A = B) (hΓ : Γ = Γ') (e : Expr (A::Γ) .exp ()) : (cast (congrArg₂ (λ Γ A => Expr (A::Γ) .exp ()) hΓ h) e).lam = cast (congrArg₂ (Expr · .val ·.not) hΓ h) e.lam := by
  subst h hΓ
  rfl

theorem congrArg₃ (f : α → β → γ → φ) {x x' : α} {y y' : β} {z z' : γ}
    (hx : x = x') (hy : y = y')  (hz : z = z'): f x y z = f x' y' z':= by subst hx hy hz; rfl

theorem Expr.cast_and_intro (hA : A = A') (hB : B = B') (hΓ : Γ = Γ') (hx : A.times B = C): cast (congrArg₂ (Expr · val ·) hΓ hx) (Expr.and_intro e₁ e₂) = cast (congrArg (Expr Γ' val) (cast (congrArg₂ (·.times · = C) hA hB) hx)) (Expr.and_intro (cast (congrArg₂ (Expr · val ·) hΓ hA) e₁) (cast (congrArg₂ (Expr · val ·) hΓ hB) e₂)) := by
  subst hA hB hΓ
  rfl

-- theorem Expr.cast_and_elim (hA : A = A') (hB : B = B') (hΓ : Γ = Γ') : cast (congrArg (Expr · exp ()) hΓ) (Expr.and_elim e₁ e₂) = Expr.and_elim (cast (congrArg₃ (fun Γ A B => Expr Γ val (Ty.times A B)) hΓ hA hB) e₁) (cast (congrArg₃ (fun Γ A B => Expr (B :: A :: Γ) exp ()) hΓ hA hB) e₂) := by
  -- subst hA hB hΓ
  -- rfl

theorem Expr.cast_app (hA : A = B) (hΓ : Γ = Γ') : cast (congrArg (Expr · exp ()) hΓ) (Expr.app e₁ e₂) = (cast (congrArg₂ (Expr · val ·.not) hΓ hA) e₁).app (cast (congrArg₂ (Expr · val ·) hΓ hA) e₂) := by
  subst hA  hΓ
  rfl

def Expr.not_not (e : Expr Γ val A) : Expr Γ val A.not.not := by
  apply Expr.lam (Expr.app Expr.zero e.lift)

def Expr.not_of_not_not_not (A : Ty) (e : Expr Γ val A.not.not.not) : Expr Γ val A.not := by
  apply Expr.lam
  apply Expr.app (e.lift)
  exact Expr.not_not Expr.zero

theorem Equiv.not_of_not_not_not (h : Equiv e₁ e₂) : Equiv (e₁.not_of_not_not_not _) (e₂.not_of_not_not_not) := by
  unfold Expr.not_of_not_not_not
  apply Equiv.lam
  refine Equiv.app ?_ Equiv.refl
  apply Equiv.ren
  assumption

@[simp]
theorem Sub.and_succ_succ (σ : Sub Γ Δ) : (Sub.and σ n.succ.succ) = (σ n).lift (B := Ty.times A B) := rfl

theorem Expr.subst_and_lift_lift (σ : Sub Γ Δ) : Expr.subst (Sub.and σ) ((t.lift (B := A)).lift (B := B)) = (Expr.subst σ t).lift := by
  induction t <;> simp [Expr.lift, Expr.ren, Expr.subst, *] at *
  case var h => cases h; rfl
  case lam ih =>
    rw [Expr.subst_ren, ← Sub.ren_comp_lift, Expr.ren_subst, ← Sub.comp_ren_lift, Expr.ren_subst, ← Sub.comp_ren_lift]
    rfl
  case app ih₁ ih₂ | and_intro ih₁ ih₂ => exact ⟨ih₁ _, ih₂ _⟩

end CPS

modular CPSFix
  namespace CPSFix

  mod inductive Tag extends CPS.Tag
  open Tag

  mod inductive PreTy extends CPS.PreTy

  mod inductive PreTy.Equiv extends CPS.PreTy.Equiv

  attribute [grind .] PreTy.Equiv.not_not PreTy.Equiv.not PreTy.Equiv.times PreTy.Equiv.refl PreTy.Equiv.symm

  attribute [grind =] Quotient.eq

  grind_pattern PreTy.Equiv.trans => PreTy.Equiv A B, PreTy.Equiv B C

  @[reducible]
  mod def Ty extends CPS.Ty

  mod def Ty.not extends CPS.Ty.not

  @[simp]
  mod def Ty.not_not extends CPS.Ty.not_not

  mod def Ty.times extends CPS.Ty.times

  @[reducible]
  mod def Tag.Data extends CPS.Tag.Data

  @[reducible]
  mod def Ctx extends CPS.Ctx

  mod def Expr._proof_1 extends CPS.Expr._proof_1

  mod inductive Expr extends CPS.Expr where
      | fix : Expr (A::A.not::Γ) exp () → Expr Γ val A.not

  -- TODO add fix

  mod def Expr.zero._proof_1 extends CPS.Expr.zero._proof_1
  mod def Expr.zero._proof_2 extends CPS.Expr.zero._proof_2
  mod def Expr.zero extends CPS.Expr.zero

  mod def Ren extends CPS.Ren
  mod def Ren.lift' extends CPS.Ren.lift'
  -- TODO fix `mod def` elab s.t it accepts decls for which auxiliary decls appear in their type
  mod def Ren.lift._proof_1 extends CPS.Ren.lift._proof_1
  mod def Ren.lift._proof_3 extends CPS.Ren.lift._proof_3
  mod def Ren.lift extends CPS.Ren.lift
  attribute [implicit_reducible] Ren Ren.lift
  mod def Ren.wk extends CPS.Ren.wk

  mod def Expr.ren._proof_1 extends CPS.Expr.ren._proof_1 where
  mod def Expr.ren extends CPS.Expr.ren where
    extend match_3 with
      | _, _, .fix e => .fix (Expr.ren r.lift.lift e)

  mod def Expr.lift extends CPS.Expr.lift

  @[implicit_reducible]
  mod def Sub extends CPS.Sub
  mod def Sub.id extends CPS.Sub.id
  mod def Sub.wk extends CPS.Sub.wk
  mod def Sub.snoc extends CPS.Sub.snoc
  mod def Sub.lift extends CPS.Sub.lift

  mod def Expr.subst extends CPS.Expr.subst where
    extend match_3 with
      | _, _, .fix e => .fix (Expr.subst σ.lift.lift e)

  mod inductive Equiv extends CPS.Equiv where
    | fix : Equiv e e' → Equiv (.fix e) (.fix e')
    | fix_beta : Equiv (.app (.fix e) v) (e.subst (Sub.id |>.snoc (.fix e) |>.snoc v))

  mod def Equiv.equiv extends CPS.Equiv.equiv
  mod def Equiv.setoid extends CPS.Equiv.setoid

  mod def Sub.and._proof_1 extends CPS.Sub.and._proof_1
  mod def Sub.and._proof_2 extends CPS.Sub.and._proof_2
  mod def Sub.and extends CPS.Sub.and

  mod def Ren.comp._proof_1 extends CPS.Ren.comp._proof_1
  mod def Ren.comp extends CPS.Ren.comp

  mod def Ren.lift_comp_lift extends CPS.Ren.lift_comp_lift

  mod def Expr.ren_of_ren_ren extends CPS.Expr.ren_of_ren_ren where finally
    intros
    simp [Expr.ren, Ren.lift_comp_lift, *]

  mod def Expr.ren_lift_wk extends CPS.Expr.ren_lift_wk

  mod def Expr.lift_ren_lift extends CPS.Expr.lift_ren_lift

  mod def Sub.ren_comp extends CPS.Sub.ren_comp

  mod def Sub.comp_ren._proof_1 extends CPS.Sub.comp_ren._proof_1
  mod def Sub.comp_ren extends CPS.Sub.comp_ren

  @[simp]
  mod def Sub.snoc_comp_ren_wk extends CPS.Sub.snoc_comp_ren_wk

  mod def Sub.comp extends CPS.Sub.comp

  @[simp]
  mod def Sub.wk_snoc_zero extends CPS.Sub.wk_snoc_zero

  @[simp]
  mod def Sub.lift_zero extends CPS.Sub.lift_zero

  @[simp]
  mod def Sub.snoc_zero extends CPS.Sub.snoc_zero

  @[simp]
  mod def Sub.snoc_succ extends CPS.Sub.snoc_succ

  @[simp]
  mod def Sub.lift_succ extends CPS.Sub.lift_succ

  mod def Sub.ren_comp_lift extends CPS.Sub.ren_comp_lift

  -- TODO fix this issue...
  mod def Expr.ren.hcongr_6' extends CPS.Expr.ren.hcongr_6

  mod def Sub.comp_ren_lift._proof_1_2 extends CPS.Sub.comp_ren_lift._proof_1_2
  mod def Sub.comp_ren_lift._proof_1_3 extends CPS.Sub.comp_ren_lift._proof_1_3
  mod def Sub.comp_ren_lift._proof_1_4 extends CPS.Sub.comp_ren_lift._proof_1_4
  mod def Sub.comp_ren_lift._proof_1_5 extends CPS.Sub.comp_ren_lift._proof_1_5
  mod def Sub.comp_ren_lift._proof_1_6 extends CPS.Sub.comp_ren_lift._proof_1_6
  mod def Sub.comp_ren_lift._proof_1_7 extends CPS.Sub.comp_ren_lift._proof_1_7
  mod def Sub.comp_ren_lift._proof_1_8 extends CPS.Sub.comp_ren_lift._proof_1_8
  mod def Sub.comp_ren_lift._proof_1_9 extends CPS.Sub.comp_ren_lift._proof_1_9
  mod def Sub.comp_ren_lift._proof_1_10 extends CPS.Sub.comp_ren_lift._proof_1_10
  mod def Sub.comp_ren_lift._proof_1_11 extends CPS.Sub.comp_ren_lift._proof_1_11
  mod def Sub.comp_ren_lift._proof_1_12 extends CPS.Sub.comp_ren_lift._proof_1_12
  mod def Sub.comp_ren_lift._proof_1_13 extends CPS.Sub.comp_ren_lift._proof_1_13
  mod def Sub.comp_ren_lift extends CPS.Sub.comp_ren_lift

  mod def Sub.wk_of_lift_comp_ren_wk extends CPS.Sub.wk_of_lift_comp_ren_wk

  mod def Sub.head extends CPS.Sub.head
  mod def Sub.tail extends CPS.Sub.tail
  mod def Sub.eta  extends CPS.Sub.eta

  mod def Sub.Zshift' extends CPS.Sub.Zshift'

  mod def Sub.Zshift extends CPS.Sub.Zshift

  mod def Sub.idR extends CPS.Sub.idR

  @[simp]
  mod def Expr.subst_id extends CPS.Expr.subst_id where
    finally
      intros
      simp [Expr.subst, Sub.Zshift, *]

  @[simp]
  mod def Sub.idL extends CPS.Sub.idL

  mod def Expr.subst_ren extends CPS.Expr.subst_ren where
    finally
      intro _ _ _ ih _ _ _ _
      simp [Expr.subst, Expr.ren, Sub.ren_comp_lift, *]

  @[simp]
  mod def Ren.lift_succ extends CPS.Ren.lift_succ

  mod def Expr.ren_subst extends CPS.Expr.ren_subst where finally
    intros
    simp [Expr.ren, Expr.subst, Sub.comp_ren_lift, *]

  mod def Expr.lift_subst_lift extends CPS.Expr.lift_subst_lift where finally
    intros
    simp [Expr.lift, Expr.ren, Expr.subst]
    rw [Expr.subst_ren, ← Sub.ren_comp_lift, Expr.ren_subst, ← Sub.comp_ren_lift, ← Sub.comp_ren_lift , ← Sub.ren_comp_lift]
    rfl

  @[simp]
  mod def Sub.comp_lift extends CPS.Sub.comp_lift

  mod def Expr.subst_subst extends CPS.Expr.subst_subst where finally
    intros
    simp only [Sub.comp_lift, Expr.subst, *]

  mod def Expr.subst.hcongr_6' extends CPS.Expr.subst.hcongr_6
  mod def Sub.comp_comp_ren extends CPS.Sub.comp_comp_ren

  mod def Sub.comp_ren_comp_ren._proof_1_3 extends CPS.Sub.comp_ren_comp_ren._proof_1_3
  mod def Sub.comp_ren_comp_ren._proof_1_5 extends CPS.Sub.comp_ren_comp_ren._proof_1_5
  mod def Sub.comp_ren_comp_ren._proof_1_6 extends CPS.Sub.comp_ren_comp_ren._proof_1_6
  mod def Sub.comp_ren_comp_ren extends CPS.Sub.comp_ren_comp_ren
  mod def Sub.comp_comp extends CPS.Sub.comp_comp

  mod def Expr.cast_val._proof_1 extends CPS.Expr.cast_val._proof_1
  mod def Expr.cast_val extends CPS.Expr.cast_val
  mod def Expr.cast_val' extends CPS.Expr.cast_val'

  mod def Equiv.ren extends CPS.Equiv.ren where
    finally
    · intros _ _ _ _ _ ih _ _
      apply Equiv.fix
      apply ih
    · intros _ _ e v _ r
      simp [Expr.ren]
      have : (Expr.ren r (Expr.subst ((Sub.id.snoc e.fix).snoc v) e)) = (Expr.subst ((Sub.id.snoc (Expr.ren r.lift.lift e).fix).snoc (Expr.ren r v)) (Expr.ren r.lift.lift e)) := by
        simp [Expr.ren_subst, Expr.subst_ren]
        congr 1
        funext x
        cases x using Fin.cases
        case zero => rfl
        case succ x =>
          cases x using Fin.cases
          · rfl
          · symm
            apply Expr.cast_val'
      rw [this]
      apply CPSFix.Equiv.fix_beta

  mod def Equiv.subst extends CPS.Equiv.subst where finally
    · intro _ _ _ _ _ ih _ _
      apply Equiv.fix
      apply ih
    · intros _ _ e v _ σ
      simp [Expr.subst]
      have : (Expr.subst σ (Expr.subst ((Sub.id.snoc e.fix).snoc v) e)) = (Expr.subst ((Sub.id.snoc (Expr.subst σ.lift.lift e).fix).snoc (Expr.subst σ v)) (Expr.subst σ.lift.lift e)) := by
        simp [Expr.subst_subst]
        congr 1
        funext x
        cases x using Fin.cases
        case zero => rfl
        case succ x =>
          cases x using Fin.cases
          · rfl
          · simp [Sub.comp, Expr.lift, Expr.ren_subst]
            rfl
      rw [this]
      apply Equiv.fix_beta

  mod def Equiv.cast extends CPS.Equiv.cast

  mod def Expr.cast_subst extends CPS.Expr.cast_subst
  mod def Expr.cast_lam extends CPS.Expr.cast_lam

  mod def Expr.not_not extends CPS.Expr.not_not

  mod def Expr.not_of_not_not_not extends CPS.Expr.not_of_not_not_not
  mod def Equiv.not_of_not_not_not extends CPS.Equiv.not_of_not_not_not

  @[simp]
  mod def Sub.and_succ_succ extends CPS.Sub.and_succ_succ

  mod def Expr.subst_and_lift_lift extends CPS.Expr.subst_and_lift_lift where
    finally
      all_goals
        intros
        simp [Expr.lift, Expr.ren, Expr.subst, Expr.ren_subst, Expr.subst_ren, ← Sub.ren_comp_lift, ← Sub.comp_ren_lift, ←  Sub.comp_ren_comp_ren, *] at *
        rfl

end CPSFix
modular end CPSFix

modular CPSNat
  namespace CPSNat

  mod inductive Tag extends CPS.Tag
  open Tag

  mod inductive PreTy extends CPS.PreTy where
    | nat

  mod inductive PreTy.Equiv extends CPS.PreTy.Equiv

  attribute [grind .] PreTy.Equiv.not_not PreTy.Equiv.not PreTy.Equiv.times PreTy.Equiv.refl PreTy.Equiv.symm

  attribute [grind =] Quotient.eq

  grind_pattern PreTy.Equiv.trans => PreTy.Equiv A B, PreTy.Equiv B C

  @[reducible]
  mod def Ty extends CPS.Ty

  def Ty.nat : Ty := ⟦ PreTy.nat ⟧

  mod def Ty.not extends CPS.Ty.not

  @[simp]
  mod def Ty.not_not extends CPS.Ty.not_not

  mod def Ty.times extends CPS.Ty.times

  @[reducible]
  mod def Tag.Data extends CPS.Tag.Data

  @[reducible]
  mod def Ctx extends CPS.Ctx

  mod def Expr._proof_1 extends CPS.Expr._proof_1

  mod inductive Expr extends CPS.Expr where
    | Z : Expr Γ val .nat
    | S : Expr Γ val .nat → Expr Γ val .nat
    | nat_match : Expr Γ exp () → Expr (Ty.nat::Γ) exp () → Expr Γ val Ty.nat.not

  mod def Expr.zero._proof_1 extends CPS.Expr.zero._proof_1
  mod def Expr.zero._proof_2 extends CPS.Expr.zero._proof_2
  mod def Expr.zero extends CPS.Expr.zero

  mod def Ren extends CPS.Ren
  mod def Ren.lift' extends CPS.Ren.lift'
  -- TODO fix `mod def` elab s.t it accepts decls for which auxiliary decls appear in their type
  mod def Ren.lift._proof_1 extends CPS.Ren.lift._proof_1
  mod def Ren.lift._proof_3 extends CPS.Ren.lift._proof_3
  mod def Ren.lift extends CPS.Ren.lift
  attribute [implicit_reducible] Ren Ren.lift
  mod def Ren.wk extends CPS.Ren.wk

  mod def Expr.ren._proof_1 extends CPS.Expr.ren._proof_1 where
  mod def Expr.ren extends CPS.Expr.ren where
    extend match_3 with
      | _, _, .Z => .Z
      | _, _, .S n => .S (Expr.ren r n)
      | _, _, .nat_match P0 PS => .nat_match (Expr.ren r P0) (Expr.ren r.lift PS)

  mod def Expr.lift extends CPS.Expr.lift

  mod def Sub extends CPS.Sub
  attribute [implicit_reducible] Sub
  mod def Sub.id extends CPS.Sub.id
  mod def Sub.wk extends CPS.Sub.wk
  mod def Sub.snoc extends CPS.Sub.snoc
  mod def Sub.lift extends CPS.Sub.lift

  mod def Expr.subst extends CPS.Expr.subst where
    extend match_3 with
      | _, _, .Z => .Z
      | _, _, .S n => .S (Expr.subst σ n)
      | _, _, .nat_match P0 PS => .nat_match (Expr.subst σ P0) (Expr.subst σ.lift PS)

  mod inductive Equiv extends CPS.Equiv where
    | S : Equiv n k → Equiv (.S n) (.S k)
    | nat_match : Equiv P0 P0' → Equiv PS PS' → Equiv (.nat_match P0 PS) (.nat_match P0' PS')
    | match_zero : Equiv (.app (.nat_match P0 PS) .Z) P0
    | match_succ : Equiv (.app (.nat_match P0 PS) (.S n)) (PS.subst (Sub.id.snoc n))

  mod def Equiv.equiv extends CPS.Equiv.equiv
  mod def Equiv.setoid extends CPS.Equiv.setoid

  mod def Sub.and._proof_1 extends CPS.Sub.and._proof_1
  mod def Sub.and._proof_2 extends CPS.Sub.and._proof_2
  mod def Sub.and extends CPS.Sub.and

  mod def Ren.comp._proof_1 extends CPS.Ren.comp._proof_1
  mod def Ren.comp extends CPS.Ren.comp

  mod def Ren.lift_comp_lift extends CPS.Ren.lift_comp_lift

  mod def Expr.ren_of_ren_ren extends CPS.Expr.ren_of_ren_ren where finally
    all_goals intros; simp [Expr.ren, Ren.lift_comp_lift, *]

  mod def Expr.ren_lift_wk extends CPS.Expr.ren_lift_wk

  mod def Expr.lift_ren_lift extends CPS.Expr.lift_ren_lift

  mod def Sub.ren_comp extends CPS.Sub.ren_comp

  mod def Sub.comp_ren._proof_1 extends CPS.Sub.comp_ren._proof_1
  mod def Sub.comp_ren extends CPS.Sub.comp_ren

  @[simp]
  mod def Sub.snoc_comp_ren_wk extends CPS.Sub.snoc_comp_ren_wk

  mod def Sub.comp extends CPS.Sub.comp

  @[simp]
  mod def Sub.wk_snoc_zero extends CPS.Sub.wk_snoc_zero

  @[simp]
  mod def Sub.lift_zero extends CPS.Sub.lift_zero

  @[simp]
  mod def Sub.snoc_zero extends CPS.Sub.snoc_zero

  @[simp]
  mod def Sub.snoc_succ extends CPS.Sub.snoc_succ

  @[simp]
  mod def Sub.lift_succ extends CPS.Sub.lift_succ

  mod def Sub.ren_comp_lift extends CPS.Sub.ren_comp_lift

  mod def Expr.ren.hcongr_6' extends CPS.Expr.ren.hcongr_6

  mod def Sub.comp_ren_lift._proof_1_2 extends CPS.Sub.comp_ren_lift._proof_1_2
  mod def Sub.comp_ren_lift._proof_1_3 extends CPS.Sub.comp_ren_lift._proof_1_3
  mod def Sub.comp_ren_lift._proof_1_4 extends CPS.Sub.comp_ren_lift._proof_1_4
  mod def Sub.comp_ren_lift._proof_1_5 extends CPS.Sub.comp_ren_lift._proof_1_5
  mod def Sub.comp_ren_lift._proof_1_6 extends CPS.Sub.comp_ren_lift._proof_1_6
  mod def Sub.comp_ren_lift._proof_1_7 extends CPS.Sub.comp_ren_lift._proof_1_7
  mod def Sub.comp_ren_lift._proof_1_8 extends CPS.Sub.comp_ren_lift._proof_1_8
  mod def Sub.comp_ren_lift._proof_1_9 extends CPS.Sub.comp_ren_lift._proof_1_9
  mod def Sub.comp_ren_lift._proof_1_10 extends CPS.Sub.comp_ren_lift._proof_1_10
  mod def Sub.comp_ren_lift._proof_1_11 extends CPS.Sub.comp_ren_lift._proof_1_11
  mod def Sub.comp_ren_lift._proof_1_12 extends CPS.Sub.comp_ren_lift._proof_1_12
  mod def Sub.comp_ren_lift._proof_1_13 extends CPS.Sub.comp_ren_lift._proof_1_13
  mod def Sub.comp_ren_lift extends CPS.Sub.comp_ren_lift

  mod def Sub.wk_of_lift_comp_ren_wk extends CPS.Sub.wk_of_lift_comp_ren_wk

  mod def Sub.head extends CPS.Sub.head
  mod def Sub.tail extends CPS.Sub.tail
  mod def Sub.eta  extends CPS.Sub.eta

  mod def Sub.Zshift' extends CPS.Sub.Zshift'

  mod def Sub.Zshift extends CPS.Sub.Zshift

  mod def Sub.idR extends CPS.Sub.idR

  @[simp]
  mod def Expr.subst_id extends CPS.Expr.subst_id where
    finally
      all_goals
        intros
        simp [Expr.subst, Sub.Zshift, *]

  @[simp]
  mod def Sub.idL extends CPS.Sub.idL

  mod def Expr.subst_ren extends CPS.Expr.subst_ren where
    finally
      all_goals
        intros
        simp [Expr.subst, Expr.ren, Sub.ren_comp_lift, *]

  @[simp]
  mod def Ren.lift_succ extends CPS.Ren.lift_succ

  mod def Expr.ren_subst extends CPS.Expr.ren_subst where finally
    all_goals
      intros
      simp [Expr.ren, Expr.subst, Sub.comp_ren_lift, *]

  mod def Expr.lift_subst_lift extends CPS.Expr.lift_subst_lift where finally
    all_goals
      intros
      simp [Expr.lift, Expr.ren, Expr.subst, *]
    · rw [Expr.subst_ren, Expr.ren_subst, Sub.wk_of_lift_comp_ren_wk]
      rfl
    · constructor
      · rw [Expr.subst_ren, Expr.ren_subst, Sub.wk_of_lift_comp_ren_wk]
        rfl
      · rw [Expr.subst_ren, ← Sub.ren_comp_lift, Expr.ren_subst, ← Sub.comp_ren_lift, Sub.wk_of_lift_comp_ren_wk]
        rfl

  @[simp]
  mod def Sub.comp_lift extends CPS.Sub.comp_lift

  mod def Expr.subst_subst extends CPS.Expr.subst_subst where finally
    all_goals
      intros
      simp only [Sub.comp_lift, Expr.subst, *]

  mod def Expr.subst.hcongr_6' extends CPS.Expr.subst.hcongr_6
  mod def Sub.comp_comp_ren extends CPS.Sub.comp_comp_ren

  mod def Sub.comp_ren_comp_ren._proof_1_3 extends CPS.Sub.comp_ren_comp_ren._proof_1_3
  mod def Sub.comp_ren_comp_ren._proof_1_5 extends CPS.Sub.comp_ren_comp_ren._proof_1_5
  mod def Sub.comp_ren_comp_ren._proof_1_6 extends CPS.Sub.comp_ren_comp_ren._proof_1_6
  mod def Sub.comp_ren_comp_ren extends CPS.Sub.comp_ren_comp_ren
  mod def Sub.comp_comp extends CPS.Sub.comp_comp


  mod def Expr.cast_val._proof_1 extends CPS.Expr.cast_val._proof_1
  mod def Expr.cast_val extends CPS.Expr.cast_val
  mod def Expr.cast_val' extends CPS.Expr.cast_val'

  mod def Equiv.ren extends CPS.Equiv.ren where
    finally
    · intros _ _ _ _ ih _ _
      apply Equiv.S
      apply ih
    · intros _ _ _ _ _ _ _  ih₁ ih₂ _ _
      apply CPSNat.Equiv.nat_match
      · apply ih₁
      · apply ih₂
    · intros
      apply CPSNat.Equiv.match_zero
    · intros _ _ e v _ r
      simp [Expr.ren]
      have : Expr.subst (Sub.id.snoc (Expr.ren r v)) (Expr.ren r.lift e) = Expr.ren r (Expr.subst (Sub.id.snoc v) e) := by
        simp [Expr.ren_subst, Expr.subst_ren]
        congr 1
        funext x
        cases x using Fin.cases
        case zero => rfl
        case succ x h => apply Expr.cast_val'
      rw [← this]
      apply CPSNat.Equiv.match_succ

  mod def Equiv.subst extends CPS.Equiv.subst where finally
    · intros _ _ _ _ ih _ _
      apply Equiv.S
      apply ih
    · intros _ _ _ _ _ _ _  ih₁ ih₂ _ _
      apply CPSNat.Equiv.nat_match
      · apply ih₁
      · apply ih₂
    · intros
      apply CPSNat.Equiv.match_zero
    · intros _ _ e v _ σ
      simp [Expr.subst]
      have : Expr.subst (Sub.id.snoc (Expr.subst σ v)) (Expr.subst σ.lift e) = Expr.subst σ (Expr.subst (Sub.id.snoc v) e) := by
        simp [Expr.subst_subst]
        congr 1
        funext x
        cases x using Fin.cases
        case zero => rfl
        case succ x h => simp [Sub.comp, Expr.lift, Expr.ren_subst]; rfl
      rw [← this]
      apply CPSNat.Equiv.match_succ

  mod def Equiv.cast extends CPS.Equiv.cast
  mod def Expr.cast_subst extends CPS.Expr.cast_subst
  mod def Expr.cast_lam extends CPS.Expr.cast_lam

  mod def Expr.not_not extends CPS.Expr.not_not

  mod def Expr.not_of_not_not_not extends CPS.Expr.not_of_not_not_not
  mod def Equiv.not_of_not_not_not extends CPS.Equiv.not_of_not_not_not

  @[simp]
  mod def Sub.and_succ_succ extends CPS.Sub.and_succ_succ

  mod def Expr.subst_and_lift_lift extends CPS.Expr.subst_and_lift_lift where
    finally
      all_goals
        intros
        simp [Expr.lift, Expr.ren, Expr.subst, Expr.ren_subst, Expr.subst_ren, ← Sub.comp_ren_comp_ren, ← Sub.ren_comp_lift, ← Sub.comp_ren_lift, *] at *
      · rfl
      · rename_i ih₁ _
        constructor
        · apply ih₁
        · rfl

end CPSNat
modular end CPSNat

modular CPSFixNat
  namespace CPSFixNat

  mod inductive Tag extends CPSFix.Tag, CPSNat.Tag
  open Tag

  mod inductive PreTy extends CPSFix.PreTy, CPSNat.PreTy

  mod inductive PreTy.Equiv extends CPSFix.PreTy.Equiv, CPSNat.PreTy.Equiv

  attribute [grind .] PreTy.Equiv.not_not PreTy.Equiv.not PreTy.Equiv.times PreTy.Equiv.refl PreTy.Equiv.symm

  attribute [grind =] Quotient.eq

  grind_pattern PreTy.Equiv.trans => PreTy.Equiv A B, PreTy.Equiv B C

  @[reducible]
  mod def Ty extends CPSFix.Ty, CPSNat.Ty

  mod def Ty.nat extends CPSNat.Ty.nat

  mod def Ty.not extends CPSFix.Ty.not, CPSNat.Ty.not

  @[simp]
  mod def Ty.not_not extends CPSFix.Ty.not_not, CPSNat.Ty.not_not

  mod def Ty.times extends CPSFix.Ty.times, CPSNat.Ty.times

  set_option match.ignoreUnusedAlts true
  @[reducible]
  mod def Tag.Data extends CPSFix.Tag.Data, CPSNat.Tag.Data

  @[reducible]
  mod def Ctx extends CPSFix.Ctx, CPSNat.Ctx

  mod def Expr._proof_1 extends CPSFix.Expr._proof_1, CPSNat.Expr._proof_1

  mod inductive Expr extends CPSFix.Expr, CPSNat.Expr
  mod def Expr.zero._proof_1 extends CPSFix.Expr.zero._proof_1, CPSNat.Expr.zero._proof_1
  mod def Expr.zero._proof_2 extends CPSFix.Expr.zero._proof_2, CPSNat.Expr.zero._proof_2
  mod def Expr.zero extends CPSFix.Expr.zero, CPSNat.Expr.zero

  mod def Ren extends CPSFix.Ren, CPSNat.Ren
  -- set_option match.ignoreUnusedAlts true in
  mod def Ren.lift' extends CPSFix.Ren.lift', CPSNat.Ren.lift'
  -- TODO fix `mod def` elab s.t it accepts decls for which auxiliary decls appear in their type
  mod def Ren.lift._proof_1 extends CPSFix.Ren.lift._proof_1, CPSNat.Ren.lift._proof_1
  mod def Ren.lift._proof_3 extends CPSFix.Ren.lift._proof_3, CPSNat.Ren.lift._proof_3
  mod def Ren.lift extends CPSFix.Ren.lift, CPSNat.Ren.lift
  attribute [implicit_reducible] Ren Ren.lift
  mod def Ren.wk extends CPSFix.Ren.wk, CPSNat.Ren.wk

  mod def Expr.ren._proof_1 extends CPSFix.Expr.ren._proof_1, CPSNat.Expr.ren._proof_1 where
  mod def Expr.ren extends CPSFix.Expr.ren, CPSNat.Expr.ren

  mod def Expr.lift extends CPSFix.Expr.lift, CPSNat.Expr.lift

  @[implicit_reducible]
  mod def Sub extends CPSFix.Sub, CPSNat.Sub

  mod def Sub.id   extends CPSFix.Sub.id, CPSNat.Sub.id
  mod def Sub.wk   extends CPSFix.Sub.wk, CPSNat.Sub.wk
  mod def Sub.snoc extends CPSFix.Sub.snoc, CPSNat.Sub.snoc
  mod def Sub.lift extends CPSFix.Sub.lift, CPSNat.Sub.lift

  mod def Expr.subst extends CPSFix.Expr.subst, CPSNat.Expr.subst

  mod inductive Equiv extends CPSFix.Equiv, CPSNat.Equiv

  mod def Equiv.equiv  extends CPSFix.Equiv.equiv, CPSNat.Equiv.equiv
  mod def Equiv.setoid extends CPSFix.Equiv.setoid, CPSNat.Equiv.setoid

  mod def Sub.and._proof_1 extends CPSFix.Sub.and._proof_1, CPSNat.Sub.and._proof_1
  mod def Sub.and._proof_2 extends CPSFix.Sub.and._proof_2, CPSNat.Sub.and._proof_2
  mod def Sub.and extends CPSFix.Sub.and, CPSNat.Sub.and

  mod def Ren.comp._proof_1 extends CPSFix.Ren.comp._proof_1, CPSNat.Ren.comp._proof_1
  mod def Ren.comp extends CPSFix.Ren.comp, CPSNat.Ren.comp

  mod def Ren.lift_comp_lift extends CPSFix.Ren.lift_comp_lift, CPSNat.Ren.lift_comp_lift

  mod def Expr.ren_of_ren_ren extends CPSFix.Expr.ren_of_ren_ren, CPSNat.Expr.ren_of_ren_ren

  mod def Expr.ren_lift_wk extends CPSFix.Expr.ren_lift_wk, CPSNat.Expr.ren_lift_wk

  mod def Expr.lift_ren_lift extends CPSFix.Expr.lift_ren_lift, CPSNat.Expr.lift_ren_lift

  mod def Sub.ren_comp extends CPSFix.Sub.ren_comp, CPSNat.Sub.ren_comp

  mod def Sub.comp_ren._proof_1 extends CPSFix.Sub.comp_ren._proof_1, CPSNat.Sub.comp_ren._proof_1
  mod def Sub.comp_ren extends CPSFix.Sub.comp_ren, CPSNat.Sub.comp_ren

  @[simp]
  mod def Sub.snoc_comp_ren_wk extends CPSFix.Sub.snoc_comp_ren_wk, CPSNat.Sub.snoc_comp_ren_wk

  mod def Sub.comp extends CPSFix.Sub.comp, CPSNat.Sub.comp

  @[simp]
  mod def Sub.wk_snoc_zero extends CPSFix.Sub.wk_snoc_zero, CPSNat.Sub.wk_snoc_zero

  @[simp]
  mod def Sub.lift_zero extends CPSFix.Sub.lift_zero, CPSNat.Sub.lift_zero

  @[simp]
  mod def Sub.snoc_zero extends CPSFix.Sub.snoc_zero, CPSNat.Sub.snoc_zero

  @[simp]
  mod def Sub.snoc_succ extends CPSFix.Sub.snoc_succ, CPSNat.Sub.snoc_succ

  @[simp]
  mod def Sub.lift_succ extends CPSFix.Sub.lift_succ, CPSNat.Sub.lift_succ

  mod def Sub.ren_comp_lift extends CPSFix.Sub.ren_comp_lift, CPSNat.Sub.ren_comp_lift

  mod def Expr.ren.hcongr_6' extends CPSFix.Expr.ren.hcongr_6', CPSNat.Expr.ren.hcongr_6'

  mod def Sub.comp_ren_lift._proof_1_2  extends CPSFix.Sub.comp_ren_lift._proof_1_2, CPSNat.Sub.comp_ren_lift._proof_1_2
  mod def Sub.comp_ren_lift._proof_1_3  extends CPSFix.Sub.comp_ren_lift._proof_1_3, CPSNat.Sub.comp_ren_lift._proof_1_3
  mod def Sub.comp_ren_lift._proof_1_4  extends CPSFix.Sub.comp_ren_lift._proof_1_4, CPSNat.Sub.comp_ren_lift._proof_1_4
  mod def Sub.comp_ren_lift._proof_1_5  extends CPSFix.Sub.comp_ren_lift._proof_1_5, CPSNat.Sub.comp_ren_lift._proof_1_5
  mod def Sub.comp_ren_lift._proof_1_6  extends CPSFix.Sub.comp_ren_lift._proof_1_6, CPSNat.Sub.comp_ren_lift._proof_1_6
  mod def Sub.comp_ren_lift._proof_1_7  extends CPSFix.Sub.comp_ren_lift._proof_1_7, CPSNat.Sub.comp_ren_lift._proof_1_7
  mod def Sub.comp_ren_lift._proof_1_8  extends CPSFix.Sub.comp_ren_lift._proof_1_8, CPSNat.Sub.comp_ren_lift._proof_1_8
  mod def Sub.comp_ren_lift._proof_1_9  extends CPSFix.Sub.comp_ren_lift._proof_1_9, CPSNat.Sub.comp_ren_lift._proof_1_9
  mod def Sub.comp_ren_lift._proof_1_10 extends CPSFix.Sub.comp_ren_lift._proof_1_10, CPSNat.Sub.comp_ren_lift._proof_1_10
  mod def Sub.comp_ren_lift._proof_1_11 extends CPSFix.Sub.comp_ren_lift._proof_1_11, CPSNat.Sub.comp_ren_lift._proof_1_11
  mod def Sub.comp_ren_lift._proof_1_12 extends CPSFix.Sub.comp_ren_lift._proof_1_12, CPSNat.Sub.comp_ren_lift._proof_1_12
  mod def Sub.comp_ren_lift._proof_1_13 extends CPSFix.Sub.comp_ren_lift._proof_1_13, CPSNat.Sub.comp_ren_lift._proof_1_13
  set_option maxHeartbeats 0 in
  mod def Sub.comp_ren_lift extends CPSFix.Sub.comp_ren_lift, CPSNat.Sub.comp_ren_lift

  mod def Sub.wk_of_lift_comp_ren_wk extends CPSFix.Sub.wk_of_lift_comp_ren_wk, CPSNat.Sub.wk_of_lift_comp_ren_wk

  mod def Sub.head extends CPSFix.Sub.head, CPSNat.Sub.head
  mod def Sub.tail extends CPSFix.Sub.tail, CPSNat.Sub.tail
  mod def Sub.eta  extends CPSFix.Sub.eta, CPSNat.Sub.eta

  mod def Sub.Zshift' extends CPSFix.Sub.Zshift', CPSNat.Sub.Zshift'

  mod def Sub.Zshift extends CPSFix.Sub.Zshift, CPSNat.Sub.Zshift

  mod def Sub.idR extends CPSFix.Sub.idR, CPSNat.Sub.idR

  @[simp]
  mod def Expr.subst_id extends CPSFix.Expr.subst_id, CPSNat.Expr.subst_id

  @[simp]
  mod def Sub.idL extends CPS.Sub.idL

  mod def Expr.subst_ren extends CPSFix.Expr.subst_ren, CPSNat.Expr.subst_ren

  @[simp]
  mod def Ren.lift_succ extends CPSFix.Ren.lift_succ, CPSNat.Ren.lift_succ

  mod def Expr.ren_subst extends CPSFix.Expr.ren_subst, CPSNat.Expr.ren_subst

  mod def Expr.lift_subst_lift extends CPSFix.Expr.lift_subst_lift , CPSNat.Expr.lift_subst_lift

  @[simp]
  mod def Sub.comp_lift extends CPSFix.Sub.comp_lift, CPSNat.Sub.comp_lift

  mod def Expr.subst_subst extends CPSFix.Expr.subst_subst , CPSNat.Expr.subst_subst

  mod def Expr.subst.hcongr_6' extends CPSFix.Expr.subst.hcongr_6', CPSNat.Expr.subst.hcongr_6'
  mod def Sub.comp_comp_ren extends CPSFix.Sub.comp_comp_ren, CPSNat.Sub.comp_comp_ren

  mod def Sub.comp_ren_comp_ren._proof_1_3 extends CPSFix.Sub.comp_ren_comp_ren._proof_1_3, CPSNat.Sub.comp_ren_comp_ren._proof_1_3
  mod def Sub.comp_ren_comp_ren._proof_1_5 extends CPSFix.Sub.comp_ren_comp_ren._proof_1_5, CPSNat.Sub.comp_ren_comp_ren._proof_1_5
  mod def Sub.comp_ren_comp_ren._proof_1_6 extends CPSFix.Sub.comp_ren_comp_ren._proof_1_6, CPSNat.Sub.comp_ren_comp_ren._proof_1_6
  mod def Sub.comp_ren_comp_ren extends CPSFix.Sub.comp_ren_comp_ren, CPSNat.Sub.comp_ren_comp_ren
  mod def Sub.comp_comp extends CPSFix.Sub.comp_comp, CPSNat.Sub.comp_comp

  mod def Expr.cast_val._proof_1 extends CPSFix.Expr.cast_val._proof_1, CPSNat.Expr.cast_val._proof_1
  mod def Expr.cast_val extends CPSFix.Expr.cast_val, CPSNat.Expr.cast_val
  mod def Expr.cast_val' extends CPSFix.Expr.cast_val', CPSNat.Expr.cast_val'

  mod def Equiv.ren extends CPSFix.Equiv.ren, CPSNat.Equiv.ren
  mod def Equiv.subst extends CPSFix.Equiv.subst, CPSNat.Equiv.subst

  mod def Equiv.cast extends CPSFix.Equiv.cast, CPSNat.Equiv.cast
  mod def Expr.cast_subst extends CPSFix.Expr.cast_subst, CPSNat.Expr.cast_subst
  mod def Expr.cast_lam   extends CPSFix.Expr.cast_lam, CPSNat.Expr.cast_lam

  mod def Expr.not_not extends CPSFix.Expr.not_not, CPSNat.Expr.not_not

  mod def Expr.not_of_not_not_not extends CPSFix.Expr.not_of_not_not_not, CPSNat.Expr.not_of_not_not_not
  mod def Equiv.not_of_not_not_not extends CPSFix.Equiv.not_of_not_not_not, CPSNat.Equiv.not_of_not_not_not

  @[simp]
  mod def Sub.and_succ_succ extends CPSFix.Sub.and_succ_succ, CPSNat.Sub.and_succ_succ

  mod def Expr.subst_and_lift_lift extends CPSFix.Expr.subst_and_lift_lift, CPSNat.Expr.subst_and_lift_lift

end CPSFixNat
modular end CPSFixNat

namespace STLC
abbrev Tag.toCPS : Tag → CPS.Tag
  | dummy => .dummy
  | val => .val
  | exp => .exp

abbrev Ty.toCPS : STLC.Ty → CPS.Ty
  | .arr A B => (A.toCPS.times B.toCPS.not).not

abbrev Ctx.toCPS (Γ : STLC.Ctx) : CPS.Ctx := Γ.map STLC.Ty.toCPS

@[simp]
theorem Ctx.toCPS_length (Γ : STLC.Ctx) : Γ.toCPS.length = Γ.length := by
  simp [toCPS]

abbrev ToCtx (Γ : STLC.Ctx) : (t : STLC.Tag) → (A: t.Data) → CPS.Ctx
  | .exp, A => A.toCPS.not::Γ.toCPS
  | _,_ => Γ.toCPS

abbrev Tag.ToData : (t : STLC.Tag) → (A: t.Data) → t.toCPS.Data
  | .exp, _ | .dummy,_ => ()
  | .val, A => A.toCPS

abbrev ToExprType (Γ : STLC.Ctx) (t : STLC.Tag) (A: t.Data) : Type :=
  CPS.Expr (ToCtx Γ t A) t.toCPS (t.ToData A)

def Expr.toCPS : Expr Γ t A → STLC.ToExprType Γ t A
  | var ⟨n,h₁⟩ h₂ => .var ⟨n,by simp [*]⟩ (by simp [*]; congr)
  | ret v => .app .zero v.toCPS.lift
  | lam e => .lam (e.toCPS.subst (CPS.Sub.and CPS.Sub.id))
  | @app _ A B e e' => by
    have e := CPS.Expr.not_of_not_not_not _ e.toCPS.lam
    have e' := e'.toCPS.lam
    rw [CPS.Ty.not_not] at e'
    apply CPS.Expr.app (e.subst CPS.Sub.id.wk)
    refine CPS.Expr.and_intro e'.lift CPS.Expr.zero
@[simp]
theorem Ctx.getElem_toCPS (Γ : STLC.Ctx) (n : Nat) (h : n < Γ.length) :
  Γ[n].toCPS = Γ.toCPS[n]'(STLC.Ctx.toCPS_length _ ▸ h) := by
    induction Γ generalizing n
    case nil => contradiction
    case cons head tail ih  =>
      cases n
      · simp [toCPS, *] at *
      · simp [toCPS] at *

def Ren.toCPS (ρ : Ren Γ Δ) : CPS.Ren Γ.toCPS Δ.toCPS where
  val n := (ρ.val (n.cast (Ctx.toCPS_length _))).cast (Ctx.toCPS_length _).symm
  property n := by
    simp only [Fin.getElem_fin, Fin.val_cast] at *
    rw [← STLC.Ctx.getElem_toCPS, ← STLC.Ctx.getElem_toCPS]
    congr 1
    exact ρ.property (n.cast (Ctx.toCPS_length _))

@[simp]
theorem Ren.lift_toCPS (ρ : Ren Γ Δ) : (ρ.lift (A := A)).toCPS = ρ.toCPS.lift := by
  obtain ⟨ρ,_⟩ := ρ
  rw [lift, CPS.Ren.lift, Ren.toCPS]
  congr
  funext n
  cases n using Fin.cases <;> rfl

def Sub.toCPS (σ : Sub Γ Δ) : CPS.Sub Γ.toCPS Δ.toCPS := fun n => by
  have := (σ (Fin.cast (Ctx.toCPS_length _) n)).toCPS
  simp only [Fin.getElem_fin, Fin.val_cast, ToExprType, ToCtx, Ctx.getElem_toCPS] at this
  exact this

set_option allowUnsafeReducibility true in
attribute [local reducible] List.map in
theorem Expr.ren_toCPS (e : Expr Δ t A) (ρ : Ren Γ Δ) : (e.ren ρ).toCPS = (match t with | .exp => e.toCPS.ren ρ.toCPS.lift | .val => e.toCPS.ren ρ.toCPS) := by
  induction e generalizing Γ <;> simp [Expr.ren, Expr.toCPS, CPS.Expr.ren, *] at *
  case var h =>
    cases h
    simp only [Fin.getElem_fin]
    rfl
  case ret =>
    constructor
    · rfl
    · rw [CPS.Expr.lift_ren_lift]
  case lam =>
    rw [CPS.Expr.ren_subst, CPS.Expr.subst_ren]
    congr 1
    funext x
    cases x using Fin.cases
    case zero => rfl
    case succ n =>
      cases n using Fin.cases
      · rfl
      · rw [CPS.Sub.comp_ren, CPS.Sub.ren_comp]
        simp [CPS.Ren.lift_succ, Ren.toCPS]
        apply CPS.Expr.cast_val'
  case app A B a b iha ihb =>
    simp [CPS.Expr.subst, CPS.Expr.ren, CPS.Expr.subst_ren, CPS.Expr.lift, CPS.Expr.ren_subst, CPS.Expr.not_of_not_not_not, ← CPS.Sub.comp_ren_lift, ← CPS.Sub.ren_comp_lift, CPS.Expr.ren_of_ren_ren]
    and_intros
    · congr
      funext x
      cases x using Fin.cases
      case zero => rfl
      case succ x => apply CPS.Expr.cast_val'
    · rfl
    · rw [CPS.Expr.cast_ren]
      all_goals try first | rfl | rw [CPS.Ty.not_not]
      simp only [cast_eq]
      rw [CPS.Expr.cast_ren]
      all_goals try first | rfl | rw [CPS.Ty.not_not]
      simp only [cast_eq]
      rw [← CPS.Expr.ren, CPS.Expr.ren_of_ren_ren]
      rfl
    · rfl

set_option allowUnsafeReducibility true in
attribute [local reducible] List.map in
@[simp]
theorem Expr.lift_toCPS (e : Expr Γ t A) : (e.lift (B := B)).toCPS = (by cases t with | val => exact e.toCPS.lift | dummy => nomatch e | exp => exact (e.toCPS.subst CPS.Sub.id.wk.lift)) := by
  induction e <;> simp [CPS.Expr.subst, Expr.toCPS, CPS.Expr.lift, CPS.Expr.ren, Expr.lift, Expr.ren, CPS.Expr.ren_of_ren_ren, CPS.Expr.ren_subst, CPS.Expr.subst_ren, Expr.ren_toCPS, CPS.Expr.ren, CPS.Expr.subst, CPS.Expr.subst_subst, CPS.Expr.not_not, CPS.Expr.not_of_not_not_not, ← CPS.Ren.lift_comp_lift, CPS.Sub.comp_lift, ← CPS.Sub.comp_ren_lift, *] at *
  · rfl
  · constructor
    · rfl
    · rename_i Γ e a
      rw [← CPS.Expr.subst_id (t := CPS.Expr.ren (CPS.Ren.wk.comp Ren.wk.toCPS) e.toCPS)]
      rw [CPS.Expr.ren_subst]
      rfl
  · congr 1
    funext n
    cases n using Fin.cases
    · rfl
    case succ n =>
      cases n using Fin.cases <;> rfl
  · and_intros
    · rfl
    · rfl
    · rfl
    · rw [CPS.Expr.cast_ren, CPS.Expr.cast_subst]
      all_goals try first | rfl | rw [CPS.Ty.not_not]
      simp
      rename_i e _ _
      rw [← CPS.Expr.subst_id (t := CPS.Expr.ren CPS.Ren.wk (CPS.Expr.ren Ren.wk.toCPS.lift e.toCPS).lam)]
      rw [CPS.Expr.ren, CPS.Expr.subst, CPS.Expr.subst, CPS.Expr.ren_of_ren_ren, CPS.Expr.ren_subst]
      congr
      funext n
      cases n using Fin.cases <;> rfl
    · rfl

set_option backward.isDefEq.respectTransparency false
@[simp]
theorem Sub.lift_toCPS (σ : Sub Γ Δ) : (σ.lift (A := A)).toCPS = σ.toCPS.lift := by
  funext n
  cases n using Fin.cases
  · rfl
  case succ i =>
    simp only [List.map_cons, List.length_cons, Fin.getElem_fin, Fin.val_succ,
      List.getElem_cons_succ, toCPS, Fin.cast_succ_eq, Fin.val_cast, lift_succ, Expr.lift_toCPS,
      eq_mp_eq_cast, CPS.Sub.lift_succ]
    grind only [= List.getElem_map]

@[simp]
theorem Sub.id_toCPS : (@id Γ).toCPS = CPS.Sub.id := by
  funext ⟨n,_⟩
  rw [Sub.toCPS, id, CPS.Sub.id]
  simp
  apply CPS.Expr.cast_val
  rw [Tag.ToData]
  apply Ctx.getElem_toCPS

@[simp]
theorem Sub.snoc_toCPS (σ : Sub Γ Δ) : (σ.snoc t).toCPS = σ.toCPS.snoc t.toCPS := by
  funext ⟨n,_⟩
  cases n <;> rfl

@[simp]
theorem Sub.toCPS_apply (σ : Sub Γ Δ) : (σ.toCPS n) = (Ctx.getElem_toCPS ..) ▸ (σ (Fin.cast (Ctx.toCPS_length _) n)).toCPS := by
  rw [Sub.toCPS]
  simp only [Fin.getElem_fin, Fin.val_cast, eq_mp_eq_cast]
  grind -abstractProof --TODO get rid of

theorem _root_.CPS.Sub.wk_of_lift_comp_wk {σ : CPS.Sub Γ Δ} : (CPS.Sub.comp σ.lift (CPS.Sub.wk τ)) = (CPS.Sub.comp σ τ).wk (A := A):= by
  funext x
  rw [CPS.Sub.comp, CPS.Sub.wk, CPS.Expr.lift_subst_lift]
  rfl

set_option allowUnsafeReducibility true in
attribute [local reducible] List.map in
theorem Expr.subst_toCPS (e : Expr Δ t A) (σ : Sub Γ Δ) : (e.subst σ).toCPS = (match t with | .exp => e.toCPS.subst σ.toCPS.lift | .val => e.toCPS.subst σ.toCPS) := by
  induction e generalizing Γ <;> simp [Expr.subst, Expr.toCPS, CPS.Expr.subst, *] at *
  case var h =>
    cases h
    simp only [Fin.getElem_fin]
    grind -abstractProof  --TODO get rid of
  case ret =>
    constructor
    · rfl
    · rw [CPS.Expr.lift_subst_lift]
  case lam =>
    rw [CPS.Expr.subst_subst, CPS.Expr.subst_subst]
    congr 1
    funext x
    cases x using Fin.cases
    case zero => rfl
    case succ n =>
      cases n using Fin.cases
      · rfl
      · rw [CPS.Sub.comp, CPS.Sub.comp]
        simp [CPS.Sub.lift_succ, CPS.Expr.subst_and_lift_lift, CPS.Expr.lift_subst_lift, CPS.Sub.id, CPS.Expr.subst]
  case app ih₁ ih₂ =>
    simp [CPS.Expr.subst, CPS.Expr.ren, CPS.Expr.subst_ren, CPS.Expr.lift, CPS.Expr.ren_subst, CPS.Expr.not_of_not_not_not, ← CPS.Sub.comp_ren_lift, ← CPS.Sub.ren_comp_lift, CPS.Expr.subst_subst, CPS.Sub.wk_of_lift_comp_ren_wk]
    and_intros
    · congr 2
      funext x
      rw [CPS.Sub.comp_ren_comp, CPS.Sub.wk_of_lift_comp_ren_wk]
      rw [CPS.Sub.wk_of_lift_comp_wk, CPS.Sub.wk_of_lift_comp_wk, CPS.Sub.idR, CPS.Sub.comp, CPS.Sub.wk, CPS.Sub.wk, CPS.Expr.lift, CPS.Expr.lift, CPS.Expr.ren_of_ren_ren , ← CPS.Expr.subst_id (t := CPS.Expr.ren (CPS.Ren.wk.comp CPS.Ren.wk) (σ.toCPS x)), CPS.Expr.ren_subst]
      rfl
    · rfl
    · rw [CPS.Expr.cast_ren]
      all_goals try first | rfl | rw [CPS.Ty.not_not]
      simp only [cast_eq]
      rw [CPS.Expr.cast_subst]
      all_goals try first | rfl | rw [CPS.Ty.not_not]
      simp only [cast_eq]
      rw [← CPS.Expr.subst, CPS.Expr.subst_ren]
      rfl
    · rfl
end STLC
section Delab

open Lean PrettyPrinter Delaborator SubExpr

@[app_delab STLC.Tag.toCPS]
def delabTagToCPS : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``STLC.Tag.toCPS 1
  let arg ← withAppArg delab
  `(⟦ $arg ⟧)

@[app_delab STLC.Ty.toCPS]
def delabTyToCPS : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``STLC.Ty.toCPS 1
  let arg ← withAppArg delab
  `(⟦ $arg ⟧)

@[app_delab STLC.Ctx.toCPS]
def delabCtxToCPS : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``STLC.Ctx.toCPS 1
  let arg ← withAppArg delab
  `(⟦ $arg ⟧)

@[app_delab STLC.Expr.toCPS]
def delabExprToCPS : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``STLC.Expr.toCPS 4
  let arg ← withAppArg delab
  `(⟦ $arg ⟧)

@[app_delab CPS.Expr.app]
def delabCPSApp : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``CPS.Expr.app 4
  let v ← withAppArg delab
  let e ← withAppFn <| withAppArg delab
  `($e $v)

@[app_delab STLC.Expr.subst]
def delabSTLCsubst : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``STLC.Expr.subst 6
  let e ← withAppArg delab
  let σ ← withAppFn <| withAppArg delab
  `($e[$σ])

syntax term noWs"[" term "]ᵣ" : term

@[app_delab CPS.Expr.ren]
def delabCPSren : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``CPS.Expr.ren 6
  let e ← withAppArg delab
  let r ← withAppFn <| withAppArg delab
  `($e[$r]ᵣ)

syntax term " ᵣ∘ " term : term
syntax term " ∘ᵣ " term : term

@[app_delab CPS.Sub.ren_comp]
def delabCPSren_comp : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``CPS.Sub.ren_comp 5
  let σ ← withAppArg delab
  let ρ ← withAppFn <| withAppArg delab
  `($ρ ᵣ∘ $σ)

@[app_delab CPS.Sub.comp_ren]
def delabCPScomp_ren : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``CPS.Sub.comp_ren 5
  let ρ ← withAppArg delab
  let σ ← withAppFn <| withAppArg delab
  `($σ ∘ᵣ $ρ)

@[app_delab CPS.Sub.comp]
def delabCPScomp : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``CPS.Sub.comp 5
  let τ ← withAppArg delab
  let σ ← withAppFn <| withAppArg delab
  `($σ ∘ $τ)

@[app_delab CPS.Expr.subst]
def delabCPSsubst : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``CPS.Expr.subst 6
  let e ← withAppArg delab
  let σ ← withAppFn <| withAppArg delab
  `($e[$σ])

syntax "↑ᵣ" : term

@[app_delab CPS.Ren.wk]
def delabCPSRenwk : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``CPS.Ren.wk 2
  `(↑ᵣ)

@[app_delab CPS.Expr.zero, app_delab STLC.Expr.zero]
def delabExprZero : Delab := `(0)

end Delab
@[simp]
theorem _root_.CPS.Expr.cast_zero_subst_snoc (h : A = B) (σ : CPS.Sub Γ Δ) : (cast (congrArg (fun B => CPS.Expr (B::Δ) .val A) h) CPS.Expr.zero).subst (σ.snoc t) = cast (congrArg (CPS.Expr Γ CPS.Tag.val) h.symm) t := by
  cases h
  rfl

@[simp]
theorem _root_.CPS.Expr.zero_subst_lift (σ : CPS.Sub Γ Δ) : CPS.Expr.zero.subst (σ.lift (A := A)) = CPS.Expr.zero := by
  rfl

@[simp]
theorem _root_.CPS.Expr.cast_zero_subst_lift (h : A = B) (hΔ : Δ = Δ') (σ : CPS.Sub Γ Δ) : (cast (congrArg₂ (fun Δ B => CPS.Expr (B::Δ) .val A) hΔ.symm h) CPS.Expr.zero).subst (σ.lift) = cast (congrArg (fun B => CPS.Expr (B :: Γ) CPS.Tag.val A) h) CPS.Expr.zero := by
  subst h hΔ
  rfl

attribute [local implicit_reducible] List.map

theorem STLC.Equiv.toCPS (e e' : Expr Γ t A) (h : Equiv e e') : CPS.Equiv e.toCPS e'.toCPS := by
  induction h
  case refl => exact .refl
  case symm ih => exact .symm ih
  case trans ih₁ ih₂ => exact .trans ih₁ ih₂
  all_goals simp [Expr.toCPS]
  case ret ih =>
    apply CPS.Equiv.app .refl
    apply CPS.Equiv.ren
    assumption
  case lam ih =>
    apply CPS.Equiv.lam
    apply CPS.Equiv.subst
    assumption
  case app ih₁ ih₂ =>
    apply CPS.Equiv.app
    · apply CPS.Equiv.subst
      apply CPS.Equiv.not_of_not_not_not
      apply CPS.Equiv.lam
      assumption
    · apply CPS.Equiv.and_intro
      · apply CPS.Equiv.ren
        apply CPS.Equiv.cast _ (CPS.Ty.not_not _)
        apply CPS.Equiv.lam
        assumption
      · exact .refl
  case beta A Γ B e v =>
    sorry

modular STLCFix.toCPS (imports := STLCFix, CPSFix)
  namespace STLCFix

  mod def Tag.toCPS extends STLC.Tag.toCPS

  @[reducible]
  mod def Ty.toCPS extends STLC.Ty.toCPS

  mod def Ctx.toCPS extends STLC.Ctx.toCPS

  @[simp]
  mod def Ctx.toCPS_length extends STLC.Ctx.toCPS_length

  @[reducible]
  mod def ToCtx extends STLC.ToCtx

  @[reducible]
  mod def Tag.ToData extends STLC.Tag.ToData

  @[reducible]
  mod def ToExprType extends STLC.ToExprType

  mod def Expr.toCPS._proof_1 extends STLC.Expr.toCPS._proof_1
  mod def Expr.toCPS._proof_2 extends STLC.Expr.toCPS._proof_2
  mod def Expr.toCPS._proof_3 extends STLC.Expr.toCPS._proof_3

  mod def Expr.toCPS extends STLC.Expr.toCPS where
    extend match_1 with
      | _, _, .fix e => .fix ((Expr.toCPS e).subst (CPSFix.Sub.and CPSFix.Sub.id))

  @[simp]
  mod def Ctx.getElem_toCPS extends STLC.Ctx.getElem_toCPS

  mod def Ren.toCPS._proof_1 extends STLC.Ren.toCPS._proof_1
  mod def Ren.toCPS._proof_2 extends STLC.Ren.toCPS._proof_2
  mod def Ren.toCPS._proof_3 extends STLC.Ren.toCPS._proof_3
  mod def Ren.toCPS._proof_4 extends STLC.Ren.toCPS._proof_4
  mod def Ren.toCPS extends STLC.Ren.toCPS

  mod def Sub.toCPS._proof_1 extends STLC.Sub.toCPS._proof_1
  mod def Sub.toCPS._proof_2 extends STLC.Sub.toCPS._proof_2
  mod def Sub.toCPS extends STLC.Sub.toCPS

  mod def Equiv.toCPS extends STLC.Equiv.toCPS where
    finally
      · intros
        apply CPSFix.Equiv.fix
        exact CPSFix.Equiv.subst ‹_›
      · intros
        simp [Expr.toCPS]
        -- same challenges as the beta proof
        sorry

end STLCFix
modular end STLCFix.toCPS

modular STLCBool.toCPS (imports := STLCBool, CPSNat)
  namespace STLCBool

  @[reducible]
  mod def Tag.toCPS extends STLC.Tag.toCPS

  @[reducible]
  mod def Ty.toCPS extends STLC.Ty.toCPS where
    extend match_1 with
      | .bool => .nat

  mod def Ctx.toCPS extends STLC.Ctx.toCPS

  @[simp]
  mod def Ctx.toCPS_length extends STLC.Ctx.toCPS_length

  @[reducible]
  mod def ToCtx extends STLC.ToCtx

  @[reducible]
  mod def Tag.ToData extends STLC.Tag.ToData

  @[reducible]
  mod def ToExprType extends STLC.ToExprType

  mod def Expr.toCPS._proof_1 extends STLC.Expr.toCPS._proof_1
  mod def Expr.toCPS._proof_2 extends STLC.Expr.toCPS._proof_2
  mod def Expr.toCPS._proof_3 extends STLC.Expr.toCPS._proof_3

  mod def Expr.toCPS extends STLC.Expr.toCPS where
    extend match_1 with
      | _, _, .false => .Z
      | _, _, .true => CPSNat.Expr.Z.S
      | _, _, .ite b pt pf => (CPSNat.Expr.nat_match (Expr.toCPS pf) (Expr.toCPS pt).lift).app (Expr.toCPS b).lift

  @[simp]
  mod def Ctx.getElem_toCPS extends STLC.Ctx.getElem_toCPS

  mod def Ren.toCPS._proof_1 extends STLC.Ren.toCPS._proof_1
  mod def Ren.toCPS._proof_2 extends STLC.Ren.toCPS._proof_2
  mod def Ren.toCPS._proof_3 extends STLC.Ren.toCPS._proof_3
  mod def Ren.toCPS._proof_4 extends STLC.Ren.toCPS._proof_4
  mod def Ren.toCPS extends STLC.Ren.toCPS

  mod def Sub.toCPS._proof_1 extends STLC.Sub.toCPS._proof_1
  mod def Sub.toCPS._proof_2 extends STLC.Sub.toCPS._proof_2
  mod def Sub.toCPS extends STLC.Sub.toCPS

  mod def Equiv.toCPS extends STLC.Equiv.toCPS where
    finally
      · intro _ _ pt pf
        have := CPSNat.Equiv.match_succ (n := CPSNat.Expr.Z) (P0 := pf.toCPS) (PS := pt.toCPS.lift)
        simp [CPSNat.Expr.lift, CPSNat.Expr.ren_subst] at this
        exact this
      · intros
        apply CPSNat.Equiv.match_zero
      · intros
        apply CPSNat.Equiv.app
        · apply CPSNat.Equiv.nat_match
          · assumption
          · apply CPSNat.Equiv.ren
            assumption
        · apply CPSNat.Equiv.ren
          assumption

end STLCBool
modular end STLCBool.toCPS

modular STLCFixBool.toCPS (imports := STLCFixBool, CPSFixNat)
  namespace STLCFixBool

  @[reducible]
  mod def Tag.toCPS extends STLCFix.Tag.toCPS, STLCBool.Tag.toCPS

  @[reducible]
  mod def Ty.toCPS extends STLCFix.Ty.toCPS, STLCBool.Ty.toCPS

  mod def Ctx.toCPS extends STLCFix.Ctx.toCPS, STLCBool.Ctx.toCPS

  @[simp]
  mod def Ctx.toCPS_length extends STLCFix.Ctx.toCPS_length, STLCBool.Ctx.toCPS_length

  set_option match.ignoreUnusedAlts true
  @[reducible]
  mod def ToCtx extends STLCFix.ToCtx, STLCBool.ToCtx


  @[reducible]
  mod def Tag.ToData extends STLCFix.Tag.ToData, STLCBool.Tag.ToData

  @[reducible]
  mod def ToExprType extends STLC.ToExprType

  mod def Expr.toCPS._proof_1 extends STLC.Expr.toCPS._proof_1
  mod def Expr.toCPS._proof_2 extends STLC.Expr.toCPS._proof_2
  mod def Expr.toCPS._proof_3 extends STLC.Expr.toCPS._proof_3

  mod def Expr.toCPS extends STLC.Expr.toCPS

  @[simp]
  mod def Ctx.getElem_toCPS extends STLC.Ctx.getElem_toCPS

  mod def Ren.toCPS._proof_1 extends STLC.Ren.toCPS._proof_1
  mod def Ren.toCPS._proof_2 extends STLC.Ren.toCPS._proof_2
  mod def Ren.toCPS._proof_3 extends STLC.Ren.toCPS._proof_3
  mod def Ren.toCPS._proof_4 extends STLC.Ren.toCPS._proof_4
  mod def Ren.toCPS extends STLC.Ren.toCPS

  mod def Sub.toCPS._proof_1 extends STLC.Sub.toCPS._proof_1
  mod def Sub.toCPS._proof_2 extends STLC.Sub.toCPS._proof_2
  mod def Sub.toCPS extends STLC.Sub.toCPS

  mod def Equiv.toCPS extends STLC.Equiv.toCPS

end STLCFixBool
