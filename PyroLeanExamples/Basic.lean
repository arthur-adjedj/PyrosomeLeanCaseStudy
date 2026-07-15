import LeanALaCarte
import Mathlib.Data.Quot
set_option inductive.autoPromoteIndices false

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

def Expr.zero : Expr (A::Γ) val A := var ⟨0,Nat.zero_lt_succ _⟩ rfl

abbrev Ren (Γ Δ : Ctx) := {f : Fin Δ.length → Fin Γ.length // ∀ n, Δ[n] = Γ[f n]}

def Ren.lift' (r : Ren Γ Δ) : Fin (A::Δ).length → Fin (A::Γ).length
    | 0 => ⟨0,Nat.zero_lt_succ _⟩
    | ⟨n+1,h⟩ => (r.1 ⟨n,Nat.lt_of_succ_lt_succ h⟩).succ

def Ren.lift (r : Ren Γ Δ) : Ren (A::Γ) (A::Δ) where
  val := r.lift'
  property := fun
    | 0 => rfl
    | ⟨n+1,h⟩ => r.2 ⟨n,Nat.lt_of_succ_lt_succ h⟩

def Ren.wk : Ren (A::Γ) Γ where
  val := Fin.succ
  property _ := rfl

def Expr.ren (r : Ren Γ Δ) : Expr Δ t A → Expr Γ t A
  | .var n h₁ => .var (r.1 n) (by rw [←h₁];symm; exact r.2 n)

def Expr.lift : Expr Γ t A → Expr (B::Γ) t A := Expr.ren Ren.wk

abbrev Sub (Γ Δ : Ctx) := (n : Fin Δ.length) → Expr Γ val Δ[n]

def Sub.id : Sub Γ Γ := fun n => .var n rfl

def Sub.wk (σ : Sub Γ Δ) : Sub (A::Γ) Δ :=
  fun n => (σ n).lift

def Sub.snoc (σ : Sub Γ Δ) (t : Expr Γ val A) : Sub Γ (A::Δ)
  | ⟨0,_⟩ => t
  | ⟨n+1,h⟩ => σ ⟨n,Nat.lt_of_succ_lt_succ h⟩

def Sub.lift (σ : Sub Γ Δ) : Sub (A::Γ) (A::Δ) := σ.wk.snoc Expr.zero

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

modular (name := `STLC)
  namespace STLC

  inductive Tag extends Base.Tag where
    | exp
  open Tag

  inductive Ty extends Base.Ty where
    | arr (A B : Ty)

  @[reducible]
  mod def Tag.Data extends Base.Tag.Data where
    matcher match_1 with
      | .exp => Ty

  @[reducible]
  mod def Ctx extends Base.Ctx

  mod def Expr._proof_1 extends Base.Expr._proof_1

  inductive Expr extends Base.Expr where
    | ret : Expr Γ val A → Expr Γ exp A
    | lam : Expr (A::Γ) exp B → Expr Γ val (.arr A B)
    | app : Expr Γ exp  (.arr A B) → Expr Γ exp  A → Expr Γ exp B

  mod def Expr.zero._proof_1 extends Base.Expr.zero._proof_1
  mod def Expr.zero._proof_2 extends Base.Expr.zero._proof_2
  mod def Expr.zero extends Base.Expr.zero

  mod def Ren extends Base.Ren
  mod def Ren.lift' extends Base.Ren.lift'
  -- TODO fix `mod def` elab s.t it accepts decls for which auxiliary decls appear in their type
  mod def Ren.lift._proof_1 extends Base.Ren.lift._proof_1
  mod def Ren.lift._proof_3 extends Base.Ren.lift._proof_3
  mod def Ren.lift extends Base.Ren.lift
  mod def Ren.wk extends Base.Ren.wk

  mod def Expr.ren._proof_1 extends Base.Expr.ren._proof_1 where
  mod def Expr.ren extends Base.Expr.ren where
    matcher match_1 with
    | _, _, .ret v => .ret (Expr.ren r v)
    | _, _, .lam e => .lam (Expr.ren r.lift e)
    | _, _, .app f t => .app (Expr.ren r f) (Expr.ren r t)

  mod def Expr.lift extends Base.Expr.lift

  mod def Sub extends Base.Sub
  mod def Sub.id extends Base.Sub.id
  mod def Sub.wk extends Base.Sub.wk
  mod def Sub.snoc extends Base.Sub.snoc

  mod def Sub.lift extends Base.Sub.lift

  mod def Expr.subst extends Base.Expr.subst where
    matcher match_1 with
      | _, _, .ret v => .ret (Expr.subst σ v)
      | _, _, .lam f => .lam (Expr.subst σ.lift f)
      | _, _, .app f t => .app (Expr.subst σ f) (Expr.subst σ t)

  inductive Equiv extends Base.Equiv where
    | ret : Equiv v₁ v₂ → Equiv (.ret v₁) (.ret v₂)
    | lam : Equiv f₁ f₂ → Equiv (.lam f₁) (.lam f₂)
    | app : Equiv f₁ f₂ → Equiv t₁ t₂ → Equiv (.app f₁ t₁) (.app f₂ t₂)
    | beta : Equiv (.app (.ret (.lam e)) (.ret v)) (e.subst (Sub.id.snoc v))

  mod def Equiv.equiv extends Base.Equiv.equiv
  mod def Equiv.setoid extends Base.Equiv.setoid
end STLC

modular (name := `STLCFix)
  namespace STLCFix
  open STLC.Tag
  inductive Ty extends STLC.Ty where

  mod def Tag.Data extends STLC.Tag.Data where

  @[reducible]
  mod def Ctx extends STLC.Ctx

  mod def Expr._proof_1 extends STLC.Expr._proof_1

  inductive Expr extends STLC.Expr where
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
    matcher match_4 with
      | _, _, .fix e => .fix (Expr.ren r.lift.lift e)

  mod def Expr.lift extends STLC.Expr.lift

  mod def Sub extends STLC.Sub
  mod def Sub.id extends STLC.Sub.id
  mod def Sub.wk extends STLC.Sub.wk
  mod def Sub.snoc extends STLC.Sub.snoc
  mod def Sub.lift extends STLC.Sub.lift

  mod def Expr.subst extends STLC.Expr.subst where
    matcher match_4 with
      | _, _, .fix e => .fix (Expr.subst σ.lift.lift e)

  inductive Equiv extends STLC.Equiv where
    | fix : Equiv (.app (.ret (.fix e)) (.ret v)) (e.subst (Sub.id |>.snoc (.fix e) |>.snoc v))
end STLCFix

modular (name := `STLCBool)
  namespace STLCBool
  open STLC.Tag
  inductive Ty extends STLC.Ty where
    | bool

  mod def Tag.Data extends STLC.Tag.Data where

  @[reducible]
  mod def Ctx extends STLC.Ctx

  mod def Expr._proof_1 extends STLC.Expr._proof_1

  inductive Expr extends STLC.Expr where
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
    matcher match_4 with
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
    matcher match_4 with
      | _, _, .true => .true
      | _, _, .false => .false
      | _, _, .ite b e₁ e₂ => .ite (Expr.subst σ b) (Expr.subst σ e₁) (Expr.subst σ e₂)

  inductive Equiv extends STLC.Equiv where
    | ite_true : Equiv (.ite .true e₁ e₂) e₁
    | ite_false : Equiv (.ite .false e₁ e₂) e₂
    | ite : Equiv b b' → Equiv e₁ e₁' → Equiv e₂ e₂' → Equiv (.ite b e₁ e₂) (.ite b' e₁' e₂')

end STLCBool



-- #exit
modular (name := `CPS)
  namespace CPS

  inductive Tag extends Base.Tag where
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
    induction e <;> grind

  @[simp]
  theorem Ty.not_not (A : Ty) : A.not.not = A := by
    apply Quotient.recOnSubsingleton A (motive := fun A => (Ty.not A).not = A)
    intro a
    rw [not, not, Quotient.liftOn_mk, Quotient.liftOn_mk, Quotient.eq]
    apply PreTy.Equiv.not_not

  def Ty.times (A B: Ty) : Ty := Quotient.liftOn₂ A B (fun A B => ⟦ A.times B ⟧ ) fun a₁ a₂ b₁ b₂ e₁ e₂ => by
    induction e₁ <;> induction e₂
    <;> simp only [propext Quotient.eq, implies_true, *] at *
    <;> grind [PreTy]

  @[reducible]
  mod def Tag.Data extends Base.Tag.Data where
    matcher match_1 with
      | .exp => Unit

  @[reducible]
  mod def Ctx extends Base.Ctx

  mod def Expr._proof_1 extends Base.Expr._proof_1

  inductive Expr extends Base.Expr where
    | lam : Expr (A::Γ) exp () → Expr Γ val A.not
    | app : Expr Γ val A.not → Expr Γ val A → Expr Γ exp ()
    | and_intro : Expr Γ val A → Expr Γ val B → Expr Γ val (A.times B)
    | and_elim : Expr Γ val (A.times B) → Expr (B::A::Γ) exp () → Expr Γ exp ()

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
    matcher match_1 with
    | _, _, .lam e => .lam (Expr.ren r.lift e)
    | _, _, .app f t => .app (Expr.ren r f) (Expr.ren r t)
    | _, _, .and_intro fst snd => .and_intro (Expr.ren r fst) (Expr.ren r snd)
    | _, _, .and_elim p e => .and_elim (Expr.ren r p) (Expr.ren r.lift.lift e)

  mod def Expr.lift extends Base.Expr.lift

  mod def Sub extends Base.Sub
  attribute [implicit_reducible] Sub
  mod def Sub.id extends Base.Sub.id
  mod def Sub.wk extends Base.Sub.wk
  mod def Sub.snoc extends Base.Sub.snoc
  mod def Sub.lift extends Base.Sub.lift

  mod def Expr.subst extends Base.Expr.subst where
    matcher match_1 with
      | _, _, .lam f => .lam (Expr.subst σ.lift f)
      | _, _, .app f t => .app (Expr.subst σ f) (Expr.subst σ t)
      | _, _, .and_intro fst snd => .and_intro (Expr.subst σ fst) (Expr.subst σ snd)
      | _, _, .and_elim p e => .and_elim (Expr.subst σ p) (Expr.subst σ.lift.lift e)

  inductive Equiv extends Base.Equiv where
    | lam : Equiv f₁ f₂ → Equiv (.lam f₁) (.lam f₂)
    | app : Equiv f₁ f₂ → Equiv t₁ t₂ → Equiv (.app f₁ t₁) (.app f₂ t₂)
    | beta : Equiv (.app (.lam e) v) (e.subst (Sub.id.snoc v))
    | eta {v : Expr Γ val (.not A)}: Equiv (.lam (.app v.lift .zero)) v
    | and_intro : Equiv fst₁ fst₂ → Equiv snd₁ snd₂ → Equiv (.and_intro fst₁ snd₁) (.and_intro fst₂ snd₂)
    | and_elim :  Equiv p₁ p₂ → Equiv e₁ e₂ → Equiv (.and_elim p₁ e₁) (.and_elim p₂ e₂)
    | eta_and : Equiv (.and_elim (.and_intro fst snd) e) (e.subst (Sub.id |>.snoc snd |>.snoc fst))

  mod def Equiv.equiv extends Base.Equiv.equiv
  mod def Equiv.setoid extends Base.Equiv.setoid

end CPS

-- #exit
modular (name := `CPSFix)
  namespace CPSFix

  inductive Tag extends CPS.Tag
  open Tag

  inductive PreTy extends CPS.PreTy

  inductive PreTy.Equiv extends CPS.PreTy.Equiv

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

  inductive Expr extends CPS.Expr where
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
    matcher match_3 with
      | _, _, .fix e => .fix (Expr.ren r.lift.lift e)

  mod def Expr.lift extends CPS.Expr.lift

  mod def Sub extends CPS.Sub
  attribute [implicit_reducible] Sub
  mod def Sub.id extends CPS.Sub.id
  mod def Sub.wk extends CPS.Sub.wk
  mod def Sub.snoc extends CPS.Sub.snoc
  mod def Sub.lift extends CPS.Sub.lift

  mod def Expr.subst extends CPS.Expr.subst where
    matcher match_3 with
      | _, _, .fix e => .fix (Expr.subst σ.lift.lift e)

  inductive Equiv extends CPS.Equiv where
    | fix : Equiv (.app (.fix e) v) (e.subst (Sub.id |>.snoc (.fix e) |>.snoc v))

  mod def Equiv.equiv extends CPS.Equiv.equiv
  mod def Equiv.setoid extends CPS.Equiv.setoid

end CPSFix

def STLC.Tag.toCPS : Tag → CPS.Tag
  | dummy => .dummy
  | val => .val
  | exp => .exp

def STLC.Ty.toCPS : STLC.Ty → CPS.Ty
  | .arr A B => (A.toCPS.times B.toCPS.not).not

def STLC.Ctx.toCPS (Γ : STLC.Ctx) : CPS.Ctx := Γ.map STLC.Ty.toCPS

abbrev STLC.ToCtx (Γ : STLC.Ctx) : (t : STLC.Tag) → (A: t.Data) → CPS.Ctx
  | .exp, A => A.toCPS.not::Γ.toCPS
  | _,_ => Γ.toCPS

abbrev STLC.Tag.ToData : (t : STLC.Tag) → (A: t.Data) → t.toCPS.Data
  | .exp, _ | .dummy,_ => ()
  | .val, A => A.toCPS

abbrev STLC.ToExprType (Γ : STLC.Ctx) (t : STLC.Tag) (A: t.Data) : Type :=
  CPS.Expr (ToCtx Γ t A) t.toCPS (t.ToData A)

def STLC.Expr.toCPS : Expr Γ t A → STLC.ToExprType Γ t A
  | var ⟨n,h₁⟩ h₂ => .var ⟨n,by simp [Ctx.toCPS, *]⟩ (by simp [Ctx.toCPS, *]; congr)
  | ret v => .app .zero v.toCPS.lift
  | lam e => .lam (.and_elim .zero (e.toCPS.subst CPS.Sub.id.wk.lift.lift))
  | @app _ A B e e' => by
    have e := e.toCPS.lam
    have e' := e'.toCPS.lam
    rw [CPS.Ty.not_not] at e e'
    refine CPS.Expr.app (e.subst CPS.Sub.id.wk) (.and_intro (e'.subst CPS.Sub.id.wk) CPS.Expr.zero)

def CPS.Ren.comp (r₁ : Ren Γ Δ) (r₂ : Ren Δ Φ) : Ren Γ Φ where
  val := r₁.val ∘ r₂.val
  property n := r₂.property n |>.trans (r₁.property (r₂.val n))

theorem CPS.Expr.ren_of_ren_ren  {r₁ : Ren Γ Δ} {r₂ : Ren Δ Φ} (v : Expr Φ t A) : (v.ren r₂).ren r₁ = v.ren (r₁.comp r₂) := by
  induction v generalizing r₁ Γ Δ <;> simp [ren, Ren.comp, *]
  case lam =>
    congr 2
    funext ⟨x,_⟩
    cases x <;> rfl
  case and_elim =>
    congr 2
    funext ⟨x,_⟩
    cases x
    case zero => rfl
    case succ x _ => cases x <;> rfl

theorem CPS.Expr.ren_lift_wk {r : Ren Γ Δ} : (r.lift.comp Ren.wk) = ((Ren.wk (A := B)).comp r) := by
  simp [Ren.comp, Ren.lift, Ren.wk]
  rfl

theorem CPS.Expr.lift_ren_lift {r : Ren Γ Δ} (v : Expr Δ t A): Expr.ren r.lift v.lift = (Expr.ren r v).lift (B := B) := by
  rw [Expr.lift, Expr.lift, CPS.Expr.ren_of_ren_ren, CPS.Expr.ren_of_ren_ren]
  rfl

abbrev CPS.Ren.toSub (r : Ren Γ Δ) : Sub Γ Δ := fun n => .var (r.1 n) (r.2 n).symm

@[simp]
theorem CPS.Ren.toSub_lift (r : Ren Γ Δ) : r.lift.toSub = r.toSub.lift (A := A)  := by
  funext ⟨x,_⟩
  cases x <;> rfl

instance : Coe (CPS.Ren Γ Δ) (CPS.Sub Γ Δ) where
  coe := CPS.Ren.toSub

@[simp]
theorem CPS.Expr.ren_of_subst_ren {r : Ren Γ Δ} (e : Expr Δ t A) : e.subst r = e.ren r := by
  induction e generalizing Γ <;> simp [CPS.Ren.toSub, subst, ren, ← CPS.Ren.toSub_lift, *]
  case var h => cases h; rfl

def CPS.Sub.comp (σ₁ : Sub Γ Δ) (σ₂ : Sub Δ Φ) : Sub Γ Φ :=
  fun n => (σ₂ n).subst σ₁

@[simp]
theorem CPS.Sub.wk_snoc_zero (σ : Sub Γ Δ) : (σ.wk (A := A)).snoc Expr.zero = σ.lift := rfl

@[simp]
theorem CPS.Expr.subst_lift_zero (σ : Sub Γ Δ) : σ.lift (A := A) ⟨0,h⟩ = Expr.zero := rfl

@[simp]
theorem CPS.Expr.subst_snoc_zero (σ : Sub Γ Δ) : σ.snoc e ⟨0,h⟩ = e := rfl

@[simp]
theorem CPS.Expr.subst_snoc_succ (σ : Sub Γ Δ) : σ.snoc e ⟨n+1,h⟩ = σ ⟨n,Nat.lt_of_succ_lt_succ h⟩ := rfl

@[simp]
theorem CPS.Expr.subst_lift_succ (σ : Sub Γ Δ) : σ.lift (A := A) ⟨n+1,h⟩ = (σ ⟨n,Nat.lt_of_succ_lt_succ h⟩).lift := rfl

theorem CPS.Sub.ren_comp_lift {r : Ren Γ Δ} {σ : Sub Δ Φ} : (Sub.comp r σ).lift (A := A) = Sub.comp r.lift.toSub σ.lift := by
  funext ⟨x,_⟩
  unfold comp lift
  simp
  cases x
  · rfl
  · simp only [List.getElem_cons_succ, Expr.subst_lift_succ, Fin.getElem_fin, ← CPS.Ren.toSub_lift, CPS.Expr.ren_of_subst_ren, CPS.Expr.lift_ren_lift]

theorem CPS.Sub.wk_of_lift_comp_ren_wk {σ : Sub Γ Δ} : (Sub.comp σ.lift Ren.wk.toSub) = σ.wk (A := A) := by
  funext ⟨x,_⟩
  rw [comp, Sub.wk, Expr.lift, Ren.toSub, Ren.wk, Expr.subst]
  simp only
  unfold Fin.succ
  rw [CPS.Expr.subst_lift_succ, Expr.lift]

@[simp]
theorem CPS.Sub.comp_ren_lift {σ : Sub Γ Δ} {τ : Sub Δ Φ} : Sub.comp σ.lift τ.lift = (Sub.comp σ τ).lift (A := A) := by
  funext ⟨x,_⟩
  simp only [lift.eq_def, comp]
  cases x --generalizing  Γ Δ Φ
  case zero => rfl
  case succ n h => sorry

theorem CPS.Expr.subst_of_subst_subst  {σ₁ : Sub Γ Δ} {σ₂ : Sub Δ Φ} (v : Expr Φ t A) : (v.subst σ₂).subst σ₁ = v.subst (σ₁.comp σ₂) := by
  induction v generalizing σ₁ Γ Δ <;> simp only [subst, Fin.getElem_fin, Sub.comp, *]
  case var h =>
    cases h
    rfl
  case lam A Φ t ih =>
    rw [CPS.Sub.comp_ren_lift]
  case and_elim ih =>
    rw [CPS.Sub.comp_ren_lift,CPS.Sub.comp_ren_lift]

theorem CPS.Expr.subst_of_subst_ren  {σ : Sub Γ Δ} {r : Ren Δ Φ}  (v : Expr Φ t A) : (v.ren r).subst σ = v.subst (Sub.comp σ r) := by
  rw [← CPS.Expr.ren_of_subst_ren, CPS.Expr.subst_of_subst_subst]

theorem CPS.Expr.subst_of_ren_subst  {r : Ren Γ Δ} {σ : Sub Δ Φ} (v : Expr Φ t A) : (v.subst σ).ren r = v.subst (Sub.comp r σ) := by
  rw [← CPS.Expr.ren_of_subst_ren, CPS.Expr.subst_of_subst_subst]

theorem CPS.Sub.wk_of_ren_wk_comp {σ : Sub Γ Δ} : (Sub.comp Ren.wk.toSub σ) = σ.wk (A := A) := by
  funext x
  rw [comp, Sub.wk, Expr.lift, CPS.Expr.ren_of_subst_ren]


theorem CPS.Expr.subst_ren_wk {σ : Sub Γ Δ} (e : Expr Δ t A) : (e.subst σ).ren (Ren.wk (A := B)) = e.subst (σ.wk (A := B)) := by
  rw [CPS.Expr.subst_of_ren_subst, CPS.Sub.wk_of_ren_wk_comp]


-- theorem CPS.Sub.comp_wk {σ₁ : Sub Γ Δ} {σ₂ : Sub Δ Φ} : (σ₁.comp σ₂).wk (A := A) = σ₁.wk.comp σ₂ := by
  -- funext ⟨x,_⟩
  -- induction x generalizing σ₁ Γ Δ Φ
  -- · rw [wk,comp, comp, Expr.lift]

theorem CPS.Expr.lift_subst_lift {σ : Sub Γ Δ} (v : Expr Δ t A): Expr.subst σ.lift v.lift = (Expr.subst σ v).lift (B := B) := by
  rw [Expr.lift, Expr.lift,CPS.Expr.subst_ren_wk, CPS.Expr.subst_of_subst_ren, CPS.Sub.wk_of_lift_comp_ren_wk]

set_option allowUnsafeReducibility true in
attribute [implicit_reducible] getElem List.length

theorem CPS.Expr.cast_val {h : Γ[n] = A}(e : A = B) : e ▸ Expr.var n h = Expr.var n h' := by cases e; rfl

-- set_option linter.tacticCheckInstances true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.implicitBump true in
theorem CPS.Equiv.ren {r : Ren Γ Δ} (e₁ e₂ : CPS.Expr Δ t A) : CPS.Equiv e₁ e₂ → CPS.Equiv (e₁.ren r) (e₂.ren r) := by
  intro h
  induction h generalizing Γ
  case refl => exact .refl
  case symm ih => exact .symm ih
  case trans ih₁ ih₂ => exact .trans ih₁ ih₂
  case lam ih => exact CPS.Equiv.lam ih
  case app ih₁ ih₂ => exact CPS.Equiv.app ih₁ ih₂
  case and_intro ih₁ ih₂ => exact CPS.Equiv.and_intro ih₁ ih₂
  case and_elim ih₁ ih₂ => exact CPS.Equiv.and_elim ih₁ ih₂
  case eta v =>
    simp [Expr.ren, Expr.zero, CPS.Expr.lift_ren_lift]
    exact CPS.Equiv.eta (v := (Expr.ren r v))
  case eta_and Δ t fst snd e =>
    simp [Expr.ren]
    apply CPS.Equiv.trans
    · apply CPS.Equiv.eta_and
    · have : (e.ren r.lift.lift).subst ((Sub.id.snoc (Expr.ren r snd)).snoc (Expr.ren r fst)) = (e.subst ((Sub.id.snoc snd).snoc fst)).ren r := by
        simp [CPS.Expr.subst_of_ren_subst, CPS.Expr.subst_of_subst_ren]
        congr 1
        funext ⟨x,_⟩
        cases x
        case zero => rw [Sub.comp, ← CPS.Ren.toSub_lift, CPS.Expr.subst_lift_zero, Sub.comp, CPS.Expr.subst_snoc_zero, Expr.zero, Expr.subst, CPS.Expr.subst_snoc_zero, CPS.Expr.ren_of_subst_ren]
        case succ x h =>
          cases x
          · rw [Sub.comp, ← CPS.Ren.toSub_lift, CPS.Expr.subst_lift_succ, CPS.Ren.toSub_lift, CPS.Expr.subst_lift_zero, Sub.comp, Expr.zero, Expr.lift, Expr.ren, Ren.wk]
            simp only [List.length_cons, Nat.reduceAdd, Fin.mk_one, Fin.getElem_fin, Fin.val_one,
              List.getElem_cons_succ, List.getElem_cons_zero, Fin.zero_eta, Fin.val_zero,
              Fin.succ_zero_eq_one, Expr.ren_of_subst_ren]
            rfl
          · cbv
            apply CPS.Expr.cast_val
      rw [this]
      apply CPS.Equiv.refl
  case beta =>
    simp [Expr.ren]
    apply CPS.Equiv.trans
    · apply CPS.Equiv.beta
    · rename_i e v
      have : (e.ren r.lift).subst (Sub.id.snoc (Expr.ren r v)) = (e.subst (Sub.id.snoc v)).ren r := by
        simp [CPS.Expr.subst_of_ren_subst, CPS.Expr.subst_of_subst_ren]
        congr 1
        funext ⟨x,_⟩
        cases x
        case zero => rw [Sub.comp, CPS.Expr.subst_lift_zero, Sub.comp, CPS.Expr.subst_snoc_zero, Expr.zero, Expr.subst, CPS.Expr.subst_snoc_zero, CPS.Expr.ren_of_subst_ren]
        case succ x h =>
          cbv
          apply CPS.Expr.cast_val
      rw [this]
      apply CPS.Equiv.refl

theorem CPS.Equiv.subst {σ : Sub Γ Δ} (e₁ e₂ : CPS.Expr Δ t A)  : CPS.Equiv e₁ e₂ → CPS.Equiv (e₁.subst σ) (e₂.subst σ) := by
  intro h
  induction h generalizing Γ
  case refl => exact .refl
  case symm ih => exact .symm ih
  case trans ih₁ ih₂ => exact .trans ih₁ ih₂
  case lam ih => exact CPS.Equiv.lam ih
  case app ih₁ ih₂ => exact CPS.Equiv.app ih₁ ih₂
  case and_intro ih₁ ih₂ => exact CPS.Equiv.and_intro ih₁ ih₂
  case and_elim ih₁ ih₂ => exact CPS.Equiv.and_elim ih₁ ih₂
  case eta v =>
    simp [Expr.subst, Expr.zero, CPS.Expr.lift_subst_lift]
    exact CPS.Equiv.eta (v := (Expr.subst σ v))
  case eta_and =>
    simp [Expr.subst]
    apply CPS.Equiv.trans
    · apply CPS.Equiv.eta_and
    · rename_i fst snd e
      have : (Expr.subst ((Sub.id.snoc (Expr.subst σ snd)).snoc (Expr.subst σ fst)) (Expr.subst σ.lift.lift e)) = (Expr.subst σ (Expr.subst ((Sub.id.snoc snd).snoc fst) e)) := sorry
      rw [this]
      apply CPS.Equiv.refl
  case beta =>
    simp [Expr.subst]
    apply CPS.Equiv.trans
    · apply CPS.Equiv.beta
    · rename_i e v
      have : (Expr.subst (Sub.id.snoc (Expr.subst σ v)) (Expr.subst σ.lift e)) = (Expr.subst σ (Expr.subst (Sub.id.snoc v) e)) := sorry
      rw [this]
      apply CPS.Equiv.refl

theorem CPS.Equiv.cast  (h₁ : Expr Γ t A = Expr Γ t B) (h₂ : A = B) (e₁ e₂ : CPS.Expr Γ t A) : CPS.Equiv e₁ e₂ →
  CPS.Equiv (cast h₁ e₁) (cast h₁ e₂) := by
  cases h₂
  cases h₁
  exact id

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
    apply CPS.Equiv.and_elim .refl
    apply CPS.Equiv.subst
    assumption
  case app ih₁ ih₂ =>
    apply CPS.Equiv.app
    · apply CPS.Equiv.subst
      apply CPS.Equiv.cast _ (CPS.Ty.not_not _)
      apply CPS.Equiv.lam
      assumption
    · apply CPS.Equiv.and_intro
      · apply CPS.Equiv.subst
        apply CPS.Equiv.cast _ (CPS.Ty.not_not _)
        apply CPS.Equiv.lam
        assumption
      · exact .refl
  case beta => sorry
