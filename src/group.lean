import data.int.basic
import data.rat.basic
import tactic.rewrite_all.basic
import tactic.nth_rewrite.basic
import tactic
import data.zmod.defs
import data.zmod.basic

import init.meta.interactive

class Group  :=
  (T : Type)
  (f:  T → T → T)
  (assoc: ∀(a b c: T),  f (f a b) c  = f a (f b c) )
  (e: T)
  (identity_left: ∀(a :T), f e a = a) 
  (identity_right: ∀(a :T), f a e = a)
  (inv: T → T)
  (inv_left: ∀(a:T), f (inv a) a = e) 
  (inv_right: ∀(a:T), f a (inv a) = e) 

class abelianGroup   :=
  (G: Group)
  (comm: ∀(a b : G.T), G.f a b = G.f b a)


instance int_add_group : Group :=  
  ⟨ℤ, (+) ,int.add_assoc,  0, int.zero_add, int.add_zero,int.neg,int.add_left_neg, int.add_right_neg ⟩

/- why is this not in mathlib?-/
def add_right_rat: (∀ (a : ℚ), a + a.neg = 0)  := begin
  intro a,
  rw rat.add_comm,
  exact rat.add_left_neg a,
end 

variables { grp : Group}
variables { a b c : grp.T}
-- def grp: Group G := _inst_1
def G: Type := grp.T
def e: G := grp.e
-- def T
def f: G → G → G := grp.f
def inv: G  → G := grp.inv
@[simp] 
def assoc: ∀(a b c: G),  f (f a b) c  = f a (f b c) := grp.assoc
@[simp] 
def inv_left: ∀(a:G), f (inv a) a = e := grp.inv_left
@[simp] 
def inv_right: ∀(a:G), f  a (inv a) = e := grp.inv_right
@[simp] 
def idl: f e a  = a :=  grp.identity_left a
@[simp] 
def idr: f a e  = a :=  grp.identity_right a
@[simp] 
def il: f (inv a) a  = e :=  grp.inv_left a

-- #check il
instance q_add_group : Group := 
  ⟨ℚ , (+), rat.add_assoc, 0, rat.zero_add, rat.add_zero, rat.neg, rat.add_left_neg, add_right_rat⟩ 


@[simp]
def left_can: f a b = f a c → b = c := begin
  intro eq,
  have cong := congr (refl (f (inv a))) eq,
  repeat {rw [← assoc] at cong},
  simp at cong,
  exact cong,
end

@[simp]
def right_can: f b a = f c a → b = c := begin
  intro eq,
  have cong := congr (refl (λx, f x (inv a))) eq,
  repeat {rw [← assoc] at cong},
  simp at cong,
  exact cong,
end
@[simp]
def double_inv: inv (inv a) = a := begin
  have nna:= inv_right (inv a),
  rw  ← inv_left a at nna,
  exact left_can nna,
end

def inv_dist: inv (f a b) = f (inv b) (inv a) := begin
  apply left_can,
  rw [inv_right, assoc],
  nth_rewrite 1 ← assoc,
  nth_rewrite 0 ← assoc,
  simp,
end
variables {x: ℕ }
def d_elem (x:ℕ ): Type := bool × zmod (x)

def d_add (x: ℕ ) (a: d_elem x) (b:d_elem x) : d_elem x :=  
 ( bxor a.1  b.1,  if b.1 then b.2  - a.2 else b.2  + a.2)
def d_assoc (x:ℕ ): (∀ (a b c : d_elem x), d_add x (d_add x a b) c = d_add x a (d_add x b c)):= begin
  intros a b c,
  cases a,
  cases b,
  cases c,
  repeat{ rw d_add},
  simp,
  cases c_fst,
  any_goals {
    cases b_fst,
    repeat {simp, ring},
  },
end
def d_add_left (x): (∀ (a : d_elem x), d_add x (false, 0) a = a) := begin
  intro a,
  repeat{ rw d_add},
  simp,
end
def d_add_right (x): (∀ (a : d_elem x), d_add x a (false, 0) = a) := begin
  intro a,
  repeat{ rw d_add},
  simp,
end
def d_inv (x) (a  : d_elem x) :  d_elem x := ( a.1,  if a.1 then  a.2 else x - a.2)
def d_inv_left (x) (a: d_elem x): d_add x (d_inv x a) a = ((false:bool), (0  : zmod x)) := begin
  rw d_inv,
  rw d_add,
  simp,
  rcases a with ⟨t | f, m⟩,
  any_goals {
    -- cases b_fst,
    repeat {simp, ring_nf},
  },
  simp,{
  -- ring,
  -- simp,
  -- apply zmod.val_eq_zero,
  -- rw coe,
  -- rw lift_t,
  sorry,
  },
  -- ring_nf,
  -- repeat {simp, ring_nf},
  -- cases a_fst,
  -- simp,
  -- sorry,
  -- simp,
end
def dihedral (x: ℕ )  : Group := 
  ⟨d_elem x , d_add x,d_assoc x, (false, 0), d_add_left x,d_add_right x,d_inv x,⟩  

