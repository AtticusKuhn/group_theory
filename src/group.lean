import data.int.basic
import data.rat.basic
import tactic.rewrite_all.basic
import tactic.nth_rewrite.basic
import tactic
import data.zmod.defs
import data.zmod.basic
import data.real.basic
import data.vector.zip

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

instance r_add_group : Group :=
  ⟨ℝ , (+),add_assoc,(0:ℝ ),zero_add,add_zero,(λx,-x), add_left_neg,add_right_neg ⟩ 
def zip_assoc (n: ℕ) (g: Group) :∀ (a b c : vector Group.T n), vector.zip_with Group.f (vector.zip_with Group.f a b) c = vector.zip_with Group.f a (vector.zip_with Group.f b c) :=
begin
intros a b c,
induction n,
{
simp,
-- sorry,
},
-- rw vector.zip_with,
-- rw list.zip_with,
-- rw vector,
-- intros a b c,
-- rw vector.zip_with,
-- simp,
-- rw list.zip_with,
sorry,
end
def vec_left_id (n: ℕ ) (g:Group) : ∀ (a : vector Group.T n), vector.zip_with Group.f (vector.repeat Group.e n) a = a := 
begin
intro a,
-- induction n,{
--   simp,
-- },
induction a using vector.induction_on,
{
simp,
},
-- rw vector.zip_with,
-- rw list.zip_with,
-- simp,
sorry,
end
def vec_right_id (n: ℕ ) (g:Group) : ∀ (a : vector Group.T n), vector.zip_with Group.f a (vector.repeat Group.e n) = a := 
begin
sorry,
end
def vec_inv (n: ℕ ) (g: Group) (x : vector  g.T n) : vector g.T n := vector.map (g.inv) x
def vec_inv_left (n: ℕ ) (g: Group) : ∀ (a : vector Group.T n), vector.zip_with Group.f (vec_inv n g a) a = vector.repeat Group.e n := begin
intro a,
induction a using vector.induction_on, {
  simp,
},
rw vec_inv,
-- rw vector.map,
sorry,
end
instance vec_group (n: ℕ ) (g: Group) : Group:=
  ⟨vector g.T n, vector.zip_with g.f, zip_assoc n g ,vector.repeat g.e n,vec_left_id n g,vec_right_id n g,vec_inv n g,vec_inv_left n g,sorry⟩ 


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
  rw [d_inv,d_add],
  simp,
  rcases a with ⟨t | f, m⟩,
  any_goals {repeat {simp},},
end
def d_inv_right (x) (a: d_elem x): d_add x  a (d_inv x a)= ((false:bool), (0  : zmod x)) := begin
  rw [d_inv,d_add],
  simp,
  rcases a with ⟨t | f, m⟩,
  any_goals {repeat {simp},},
end
def dihedral (x: ℕ )  : Group := 
  ⟨d_elem x , d_add x,d_assoc x, (false, 0), d_add_left x,d_add_right x,d_inv x,d_inv_left x, d_inv_right x⟩  
-- #print (dihedral 4)
-- variables {n: ℕ}
-- bijections from [n] → [n]
def bijection (x : ℕ) : Type := {f: (fin x → (fin x)) // function.bijective  f}

-- variables {b1 b2: bijection n}
-- #check bijection
def compose_bijection (x: ℕ ) (b1: bijection x) ( b2: bijection x): bijection x := ⟨ b1.1 ∘ b2.1,function.bijective.comp b1.2 b2.2 ⟩ 
def compose_assoc (x: ℕ ) :∀ (a b c : bijection x), compose_bijection x (compose_bijection x a b) c = compose_bijection x a (compose_bijection x b c) := begin
  intros a b c,
  repeat {rw compose_bijection},
end
def bij_identity (x: ℕ ): bijection x := ⟨id, function.bijective_id ⟩ 
def id_left (x:ℕ ):∀ (a : bijection x), compose_bijection x (bij_identity x) a = a := begin
  intro a,
  rw compose_bijection,
  rw bij_identity,
  simp,
end
def id_right (x:ℕ ):∀ (a : bijection x), compose_bijection x a (bij_identity x) = a := begin
  intro a,
  rw compose_bijection,
  rw bij_identity,
  simp,
end
def bij_inv (x: ℕ ): bijection x → bijection x := sorry
def symmetric_group (x: ℕ )  : Group :=
⟨bijection x,compose_bijection x ,compose_assoc x, bij_identity x ,id_left x ,id_right x,bij_inv x,sorry,sorry ⟩  


def homomorphism (G: Group) (H:Group) (φ:G.T → H.T): Prop := ∀(x y : G.T), φ(G.f x y) = H.f (φ x) (φ y)
class hom :=
  (G: Group) 
  (H:Group)
  (φ:G.T → H.T)
  (dist: ∀(x y : G.T), φ(G.f x y) = H.f (φ x) (φ y))
class hom_param (G: Group) (H:Group)  :=
  (φ:G.T → H.T)
  (dist: ∀(x y : G.T), φ(G.f x y) = H.f (φ x) (φ y))
def isomorphism (G: Group) (H:Group) (φ:G.T → H.T) : Prop := homomorphism G H φ ∧ function.bijective φ

def homomorphic (G: Group) (H:Group) : Prop := ∃ (φ:G.T → H.T), homomorphism G H φ

def D6_homo_to_S3: homomorphic (dihedral 6) (symmetric_group 3) := begin
rw homomorphic,

sorry,
end
def proj_dist (n: ℕ ) (g: Group): 
(∀ (x y : vector g.T n.succ),
     ((λvec, vector.nth vec 0) (vector.zip_with g.f x y))
     = g.f ((λvec, vector.nth vec 0) x) ((λvec, vector.nth vec 0) y)
)
:= begin
intros x y,
simp,
end
instance projection_homomorphism (g:Group) (n :ℕ ): hom  :=
 ⟨vec_group n.succ g, g, λvec, vector.nth vec 0, proj_dist n g⟩

class Group_Action := 
  (G: Group)
  (A: Type)
  (f:  G.T → A → A)
  (dist: ∀( g1 g2: G.T), ∀(a : A), f g1 (f g2 a) = f (G.f g1 g2) a)
  (id: ∀ (a: A), f G.e a = a)

instance trivial_action (G:Group) (A: Type): Group_Action :=
  ⟨G,A, λx y, y,by simp, by simp⟩ 
def autos (G: Group) : Type := hom_param G G

-- def composition_is_auto
def compose_autos (G: Group) (a: autos G) (b: autos G): autos G :=  begin
rw autos at *,
have c : ∀ (x y : Group.T),
    ((a.φ ∘ b.φ) (Group.f x y)) =
      Group.f ((a.φ ∘ b.φ) x) ((a.φ ∘ b.φ) y),{
  intros x y,
rw function.comp,

simp,
rw b.2,
rw a.2,
},
exact ⟨function.comp a.1 b.1,  c⟩, 
end
def compose_autos_assoc (G:Group) : ∀ (a b c : autos G), compose_autos G (compose_autos G a b) c = compose_autos G a (compose_autos G b c) :=begin
  intros a b c,
  repeat{rw compose_autos},
  refl,
end
def auto_id (G:Group) : autos G := begin
rw autos,
exact ⟨id, sorry⟩ 
-- rw hom_param,
sorry,
end
instance automorphisms (G: Group) : Group := 
 ⟨ autos G,  compose_autos G, compose_autos_assoc G,auto_id G , sorry, sorry, sorry,sorry,sorry⟩ 