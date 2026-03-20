/-
Copyright (c) 2026 Scott Buckley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Buckley
-/
module

public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.DepRewrite

/-!
  This file introduces a number of new definitions and lemmas for `List.Vector`,
  in particular a number of `map` variants and their associated lemmas.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` vars.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

@[expose] public section

-- unrelated to `List.Vector` but useful in this file
lemma Fin.mk_succ {n : Nat} (i : Nat) (h : i + 1 < n + 1) :
    Fin.mk (i + 1) h = (Fin.mk (n := n) i (by omega)).succ := rfl

namespace List.Vector
variable {α β : Type*} {n m k : ℕ}

section Generic

abbrev singleton (a : α) : Vector α 1 := a ::ᵥ nil

@[grind ←] lemma cons_eq_cons {a b : α} {as bs : Vector α n} (h₁ : a = b) (h₂ : as = bs) :
    a ::ᵥ as = b ::ᵥ bs := by simp [h₁, h₂]

@[simp, grind =] lemma ofFn_zero {α : Type*} {f : Fin 0 → α} : ofFn f = nil := rfl

end Generic

section Cast
/- Helper for casting between (equivalent) `Vector` lengths.
Since it's unavoidable to occasionally use cast when working with Vectors,
this at least does it in a way that hides away the cast in a propositional
value. I've made it a rule never to add to `simp` anything that *introduces*
`cast`, but i've added plenty of rules to simp that push `cast` further
to the "outside" of an expression. -/

@[inline, expose] def cast (h : n = m) (as : Vector α n) : Vector α m :=
  ⟨as.toList, by simp only [toList_length, h]⟩

@[simp, grind =] lemma cast_refl {n : Nat} (as : Vector α n) : (as.cast rfl) = as := rfl

@[simp, grind =] theorem cast_mk {as : List α} {h₁ : as.length = n} {h₂ : n = m} :
    cast h₂ ⟨as, h₁⟩ = ⟨as, (by simp only [h₁, h₂])⟩ := rfl

@[simp, grind =] lemma cast_cast (h1 : m = n) (h2 : n = k) (as : Vector α m) :
    (as.cast h1).cast h2 = as.cast (by simp_all only) := rfl

@[simp, grind =] lemma cast_cons (h : n = m) (a : α) (as : Vector α n) :
    a ::ᵥ (as.cast h) = (a ::ᵥ as).cast (by omega) := rfl

@[simp, grind =] lemma cast_map (as : Vector α n) (f : α → β) {h : n = m} :
    (as.cast h).map f = (as.map f).cast h := by rfl

@[simp] lemma cast_f (f : {k : Nat} → Vector α k → Vector β k) (as : Vector α n) {h : n = m} :
    f (as.cast h) = (f as).cast h := by cases h ; rfl

@[simp, grind =] lemma cast_append_left (h : n = k) (as : Vector α n) (bs : Vector α m) :
    as.cast h ++ bs = (as ++ bs).cast (by omega) := rfl

@[simp, grind =] lemma cast_append_right (h : m = k) (as : Vector α n) (bs : Vector α m) :
    as ++ bs.cast h = (as ++ bs).cast (by omega) := rfl

@[simp, grind =] lemma cast_append_both {m n k i : Nat} (h₁ : n = i) (h₂ : m = k)
    (as : Vector α n) (bs : Vector α m) :
    as.cast h₁ ++ bs.cast h₂ = (as ++ bs).cast (by omega) := rfl

lemma cast_eq_symm {h : m = n} {as : Vector α n} {bs : Vector α m} (hc : as = bs.cast h) :
    bs = as.cast (by simp_all only) := by simp_all only [cast_cast, cast_refl]

end Cast

section Append
/- Some more lemmas about `List.Vector.append` (++), many of which
result in expressions using `cast`, so most are not added to `simp`. -/

lemma append_cons (as : Vector α n) (b : α) (bs : Vector α m) :
    as ++ (b ::ᵥ bs) = ((as ++ singleton b) ++ bs).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  simp only [Nat.succ_eq_add_one, append_def, append_assoc, cons_append, nil_append]
  rfl

lemma cons_append (a : α) (as : Vector α n) (bs : Vector α m) :
    a ::ᵥ as ++ bs = (a ::ᵥ (as ++ bs)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  simp only [Nat.succ_eq_add_one, cons, append_def, cons_append, cast_mk]

lemma cons_append.symm (a : α) (as : Vector α n) (bs : Vector α m) :
    a ::ᵥ (as ++ bs) = (a ::ᵥ as ++ bs).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  simp only [Nat.succ_eq_add_one, cons, append_def, List.cons_append, cast_mk]

@[simp] theorem nil_append {xs : Vector α n} :
    (nil : Vector α 0) ++ xs = xs.cast (by omega) := by
  rcases xs with ⟨xs, xs_h⟩
  simp only [append_def, List.nil_append, cast_mk]

lemma append_assoc (as : Vector α n) (bs : Vector α m) (cs : Vector α k) :
    as ++ (bs ++ cs) = (as ++ bs ++ cs).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  rcases cs with ⟨cs, rfl⟩
  simp only [append_def, List.append_assoc, cast_mk]

lemma append_assoc.symm (as : Vector α n) (bs : Vector α m) (cs : Vector α k) :
    (as ++ bs ++ cs) = (as ++ (bs ++ cs)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  rcases cs with ⟨cs, rfl⟩
  simp only [append_def, List.append_assoc, cast_mk]

lemma singleton_append (a : α) (as : Vector α n) :
    (singleton a ++ as) = (a ::ᵥ as).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp only [append_def, List.cons_append, List.nil_append, Nat.succ_eq_add_one, cons, cast_mk]

@[simp]
lemma length_append (as : Vector α n) (bs : Vector α m) :
    (as ++ bs).length = as.length + bs.length := rfl

@[simp, grind =] theorem map_append {f : α → β} {as : Vector α n} {bs : Vector α m} :
    map f (as ++ bs) = map f as ++ map f bs := by
  induction as <;> simp_all [List.Vector.cons_append]

end Append

section ofFn

theorem ofFn_succ {n} {f : Fin (n + 1) → α} : ofFn f = f 0 ::ᵥ ofFn fun i => f i.succ := rfl

theorem ofFn_succ_last {n} {f : Fin (n + 1) → α} :
    ofFn f = (ofFn fun i => f i.castSucc) ++ singleton (f (Fin.last n)) := by
  induction n with
  | zero =>
    simp only [length_append, Nat.reduceAdd, Fin.last_zero, Fin.isValue]
    simp_all only [ofFn_zero, Fin.isValue]
    rfl
  | succ n ih =>
    rw [ofFn_succ]
    conv => rhs; rw [ofFn_succ]
    rw [ih]
    simp only [length_append, Fin.succ_last, Nat.succ_eq_add_one, Fin.castSucc_zero,
      Fin.castSucc_succ]
    rfl

end ofFn

section Range
/- Implements `range`, producing a vector of `Nat`s. Various lemmas for this method
are also provided, many of which require mapping to an alternative definition `range'`. -/
def range (n : Nat) : Vector Nat n :=
  loop n nil (zero_add n)
where
  loop {m : Nat} : (k : Nat) → Vector Nat m → (inv : m+k=n) → Vector Nat n
  | 0,   acc, h => acc.cast <| by omega
  | z+1, acc, h => loop z (z ::ᵥ acc) <| by omega

@[simp, grind =] lemma range_zero :
    range 0 = nil := by
  simp [range, range.loop]

def range' : (start : Nat) → (len : Nat) → (step : Nat := 1) → Vector Nat len
  | _, 0, _ => nil
  | k, n+1, s => k ::ᵥ range' (k+s) n s

@[simp] lemma range'_zero {k s : Nat} :
    range' k 0 s = nil := by
  simp [range']

def range.loop_eq_range' (n k : Nat) :
    range.loop (n+k) k (range' k n) rfl = range' 0 (n+k) := by
  induction k generalizing n
  next => simp [loop]
  next n' k' ih =>
    specialize ih (n + 1)
    simp only [loop]
    simp only [length_append, range'] at ih
    have om : (n + (k' + 1)) = (n + 1 + k') := by omega
    rw! [om]
    exact ih

def range_eq_range' (n : Nat) :
    range n = range' 0 n := by
  have hh := range.loop_eq_range' 0 n
  simp only [length_append, range'_zero] at hh
  rewrite! [Nat.zero_add n] at hh
  simp only [range, hh]

lemma cons_append_eq_cons (n n2 m m2 : Nat) (a : α) (as : Vector α n) (bs : Vector α m)
      (cs : Vector α n2) (ds : Vector α m2) :
    (h : n2 + m2 = n + m) →
    as ++ bs = (cs ++ ds).cast h →
    a ::ᵥ as ++ bs = (a ::ᵥ (cs ++ ds)).cast (by omega) := by
  intros hxy h
  rw [cons_append, h]
  rfl

lemma range'_succ_left_cast {s n step n' : Nat} (h : n = n' + 1) :
    range' s n step = (s ::ᵥ range' (s + step) n' step).cast (Eq.symm h) := by
  rw! [h]
  simp [range']

lemma range'_append (s m n step : Nat) :
    range' s m step ++ range' (s + step * m) n step = range' s (m + n) step := by
  induction m generalizing s n
  next =>
    simp only [length_append, range'_zero, Nat.mul_zero, add_zero, nil_append]
    rw! [Nat.zero_add]
    simp only [cast_refl]
  next m ih =>
    specialize ih (s+step) n
    rw [range'_succ_left_cast (Nat.add_right_comm m 1 n)]
    simp only [length_append, range']
    rw [← ih]
    have ho : (s + step * (m + 1)) = (s + step + step * m) := by grind
    rw [ho]
    clear ho ih
    rw! [cons_append.symm]
    simp only [length_append, Nat.succ_eq_add_one, cast_cast, cast_refl]

@[simp] lemma range'_eq_singleton (s step : Nat) :
    range' s 1 step = singleton s := by simp only [range']

@[simp] lemma range_eq_singleton :
    range 1 = singleton 0 := by
  simp only [range, range.loop, Nat.succ_eq_add_one, length_append, Nat.reduceAdd, cast_refl]

theorem range'_succ {s n step : Nat} :
    range' s (n + 1) step = range' s n step ++ singleton (s + step * n) := by
  rw [← range'_append]
  simp

theorem range'_succ_left {s n step : Nat} :
    range' s (n + 1) step = s ::ᵥ range' (s+step) n step := rfl

lemma range_succ (n : Nat) :
    range (n + 1) = range n ++ singleton n := by
  simp [range_eq_range', range'_succ]

def range'_eq_List_range' (step s n : Nat) :
    range' s n step = ⟨List.range' s n step, length_range'⟩ := by
  induction n
  next => simp [nil]
  next n' ih => simp only [length_append, range'_succ, ih, append_def, range'_concat]

def range_eq_List_range (n : Nat) :
    range n = ⟨List.range n, List.length_range⟩ := by
  induction n
  next => simp [nil]
  next n ih => simp only [length_append, range_succ, ih, singleton, append_def, List.range_succ]

@[simp] lemma get_range' (n : Nat) (i : Fin n) :
    (range' 0 n).get i = i := by
  simp only [get, get_eq_getElem, range'_eq_List_range', Fin.val_cast, getElem_range', one_mul,
    zero_add]

@[simp] lemma get_range (n : Nat) (i : Fin n) :
    (range n).get i = i := by
  simp only [get, get_eq_getElem, range_eq_List_range, Fin.val_cast, getElem_range]

lemma range_n_cast (h : m = n) :
  range n = (range m).cast h := by cases h ; rfl

lemma cons_append_eq_append_append (b : α) (as : Vector α n) (bs : Vector α m) :
    as ++ (b ::ᵥ bs) = (as ++ singleton b ++ bs).cast (by omega) := by
  rw [append_cons]

lemma range_plus (n m : Nat) :
    range (n + m) = range n ++ range' n m := by
  induction m generalizing n
  next => simp
  next n' ih =>
    specialize ih (n+1)
    rw [range_n_cast (Nat.succ_add_eq_add_succ n n'), ih]
    simp only [length_append, Nat.succ_eq_add_one, range_succ, range']
    rw [cons_append_eq_append_append]
    simp only [length_append, Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd, append_nil,
      cast_refl, append_cons (bs := range' (n + 1) n')]

lemma range_eq_ofFn (n : Nat) :
    range n = ofFn (fun i : Fin n ↦ i.val) := by
  induction n
  next => simp only [range_zero, ofFn_zero]
  next n' ih =>
    rw [range_succ, ih, ofFn_succ_last]
    simp only [length_append, Fin.val_castSucc, Fin.val_last]

end Range

section MapIdx
/- Defines `mapIdx`, which is similar to `List.mapIdx`: the function being mapped also takes
the index as a parameter. This section also provides a number of related lemmas. -/
variable (f : Nat → α → β)

-- Maps elements of a vector using the function `f`, which also receives the index of the element.
@[inline] def mapIdx {n : Nat} (f : Nat → α → β) (as : List.Vector α n) : List.Vector β n :=
  match n, as with
  | 0, ⟨[], _⟩ => nil
  | i+1, ⟨a :: l, h⟩ => f 0 a ::ᵥ mapIdx (fun i a ↦ f (i+1) a) ⟨l, by simp_all⟩

@[simp, grind =]
theorem mapIdx_nil {f : Nat → α → β} : mapIdx f nil = nil := rfl

@[simp, grind =]
theorem mapIdx_cons {f : Nat → α → β} {as : Vector α n} {a : α} :
    (a ::ᵥ as).mapIdx f = f 0 a ::ᵥ as.mapIdx (fun i => f (i + 1)) := by
  rcases as with ⟨as, as_h⟩
  rfl

lemma mapIdx_eq_List_mapIdx (as : List.Vector α n) :
    as.mapIdx f = ⟨as.toList.mapIdx f, by simp only [length_mapIdx, toList_length]⟩ := by
  induction as generalizing f with
  | nil => rfl
  | cons ih =>
    expose_names
    specialize ih (fun i ↦ f (i+1))
    simp only [Nat.succ_eq_add_one, length_append, mapIdx_cons, toList_cons, List.mapIdx_cons]
    rw [←cons] <;> simp_all

@[simp, grind =]
theorem mapIdx_append {as : Vector α n} {bs : Vector α m} :
    (as ++ bs).mapIdx f = as.mapIdx f ++ bs.mapIdx fun i => f (i + n) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  simp [mapIdx_eq_List_mapIdx, append_def, List.mapIdx_append]

@[simp, grind =] theorem mapIdx_concat {as : Vector α n} {a : α} :
    (as ++ singleton a).mapIdx f = as.mapIdx f ++ singleton (f n a) := by
  simp only [length_append, mapIdx_append, mapIdx_cons, zero_add, mapIdx_nil]

theorem mapIdx_singleton {a : α} : mapIdx f (singleton a) = singleton (f 0 a) := by
  simp only [mapIdx_cons, length_append, mapIdx_nil]

@[simp, grind =] theorem mapIdx_mapIdx {γ : Type*} {as : Vector α n}
    {f : Nat → α → β} {g : Nat → β → γ} :
    (as.mapIdx f).mapIdx g = as.mapIdx (fun i => g i ∘ f i) := by
  simp only [mapIdx_eq_List_mapIdx, toList_mk, List.mapIdx_mapIdx]

@[simp] lemma cast_mapIdx (as : Vector α n) (f : Nat → α → β) {h : n = m} :
    (as.cast h).mapIdx f = (as.mapIdx f).cast h := by
  rcases as with ⟨as, rfl⟩
  simp only [cast_mk, mapIdx_eq_List_mapIdx, toList_mk]

@[simp, grind =]
lemma get_mapIdx (as : Vector α n) (i : Fin n) (f : Nat → α → β) :
    (as.mapIdx f).get i = f i (as.get i) := by
  induction as generalizing f
  next =>
    rcases i with ⟨i, i_h⟩
    cases i_h
  next n_1 a as i_h =>
    simp_all only [Nat.succ_eq_add_one, length_append, mapIdx_cons]
    rcases i with ⟨i, i_lt⟩
    cases i
    next => simp only [length_append, Nat.succ_eq_add_one, Fin.zero_eta, get_zero, head_cons]
    next i' =>
      simp only [← Nat.succ_eq_add_one]
      rw [Fin.mk_succ, get_cons_succ, get_cons_succ, i_h]

@[simp, grind =]
lemma mapIdx_id (as : Vector α n) :
    as.mapIdx (fun _ a ↦ a) = as := by
  induction as
  · rfl
  · expose_names
    simp only [Nat.succ_eq_add_one, length_append, mapIdx_cons, h]

lemma mapIdx_idx (as : Vector α n) :
    as.mapIdx (fun i _ ↦ i) = range n := by
  apply ext
  simp only [get_mapIdx, get_range, implies_true]

end MapIdx

section MapFinIdx
/- Defines `mapFinIdx`, which is similar to `mapIdx`, but the function is also passed a proof that
the index is less than the size of the vector. -/

@[inline] def mapFinIdx {n : Nat} (f : (i : Nat) → α → (i < n) → β) (as : List.Vector α n) :
    List.Vector β n :=
  match n, as with
  | 0, ⟨[], _⟩ => nil
  | n'+1, ⟨a :: l, h⟩ => f 0 a (by omega) ::ᵥ mapFinIdx (n := n')
      (fun i a inv ↦ f (i+1) a (by simp_all)) ⟨l, by simp_all⟩

@[simp, grind =]
theorem mapFinIdx_nil {f : (i : Nat) → α → (i < 0) → β} : mapFinIdx f nil = nil := rfl

@[simp, grind =]
theorem mapFinIdx_cons {f : (i : Nat) → α → (i < n.succ) → β} {as : Vector α n} {a : α} :
    (a ::ᵥ as).mapFinIdx f = f 0 a (by omega) ::ᵥ
      as.mapFinIdx (fun i a inv => f (i + 1) a (by omega)) := by
  rcases as with ⟨as, as_h⟩
  rfl

lemma mapFinIdx_eq_List_mapFinIdx (as : List.Vector α n) {f : (i : Nat) → α → (i < n) → β} :
    as.mapFinIdx f = ⟨as.toList.mapFinIdx (fun i a inv ↦ f i a (by simp_all)), by simp_all⟩ := by
  induction as
  next => rfl
  next n' a as ih =>
    simp only [Nat.succ_eq_add_one, length_append, mapFinIdx_cons, toList_cons, List.mapFinIdx_cons]
    specialize ih (f := fun i a inv ↦ f (i+1) a (by omega))
    rw [←cons] <;> simp_all

@[grind =]
theorem mapFinIdx_append {as : Vector α n} {bs : Vector α m} {f : (i : Nat) → α → (i < n + m) → β} :
    (as ++ bs).mapFinIdx f = as.mapFinIdx (fun i a h ↦ f i a  <| by omega) ++
      bs.mapFinIdx fun i a h => f (i + n) a (by omega) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  simp only [length_append, append_def, mapFinIdx_eq_List_mapFinIdx, toList_mk, mapFinIdx_append]

@[simp, grind =]
theorem mapFinIdx_concat {as : Vector α n} {a : α} {f : (i : Nat) → α → (i < n + 1) → β} :
    (as ++ singleton a).mapFinIdx f = as.mapFinIdx (fun i a h ↦ f i a (by omega)) ++
      singleton (f n a (by omega)) := by
  simp only [length_append, mapFinIdx_append, mapFinIdx_cons, zero_add, mapFinIdx_nil]

@[simp, grind =]
theorem mapFinIdx_singleton {a : α} {f : (i : Nat) → α → (i < 1) → β} :
    mapFinIdx f (singleton a) = singleton (f 0 a (by omega)) := by
  simp only [mapFinIdx_cons, length_append, mapFinIdx_nil]

@[simp, grind =]
theorem mapFinIdx_mapFinIdx {γ : Type*} {as : Vector α n}
    {f : (i : Nat) → α → (i < n) → β} {g : (i : Nat) → β → (i < n) → γ} :
    (as.mapFinIdx f).mapFinIdx g = as.mapFinIdx fun i a inv ↦ g i (f i a inv) inv := by
  simp only [mapFinIdx_eq_List_mapFinIdx, toList_mk, List.mapFinIdx_mapFinIdx]

@[simp]
lemma cast_mapFinIdx (as : Vector α n) (f : (i : Nat) → α → (i < m) → β) {h : n = m} :
    (as.cast h).mapFinIdx f = (as.mapFinIdx fun i a h ↦ f i a (by omega)).cast h := by
  rcases as with ⟨as, rfl⟩
  simp only [cast_mk, mapFinIdx_eq_List_mapFinIdx, toList_mk]

@[simp]
lemma get_mapFinIdx (as : Vector α n) (i : Fin n) (f : (i : Nat) → α → (i < n) → β) :
    (as.mapFinIdx f).get i = f i (as.get i) i.isLt := by
  induction as with
  | nil => { rcases i with ⟨i, ⟨⟩⟩ } --fixme: not ure why these braces are needed here
  | @cons n_1 a as ih =>
    simp_all only [Nat.succ_eq_add_one, length_append, mapFinIdx_cons]
    rcases i with ⟨i, i_lt⟩
    cases i with
    | zero => simp only [length_append, Nat.succ_eq_add_one, Fin.zero_eta, get_zero, head_cons]
    | succ i' => rw [Fin.mk_succ, get_cons_succ, get_cons_succ, ih, Fin.succ_mk]

lemma mapFinIdx_id (as : Vector α n) :
    as.mapFinIdx (fun _ a _ ↦ a) = as := by
  induction as
  next => rfl
  next n' a as ih =>
    simp only [Nat.succ_eq_add_one, length_append, mapFinIdx_cons, ih]

lemma mapFinIdx_idx (as : Vector α n) :
    as.mapFinIdx (fun i _ _ ↦ i) = range n := by
  apply ext
  simp only [get_mapFinIdx, get_range, implies_true]

end MapFinIdx

section mapM

@[inline] def mapM {m} [Monad m] {n : Nat} (f : α → m β) (as : List.Vector α n) :
    m (List.Vector β n) :=
  match n, as with
  | 0, _ => pure nil
  | _+1, as => return (← f as.head) ::ᵥ (← as.tail.mapM f)

@[simp, grind =]
theorem mapM_nil {m} [Monad m] (f : α → m β) : mapM f nil = pure nil := rfl

@[simp, grind =]
theorem mapM_cons {m} [Monad m] (f : α → m β) {as : Vector α n} {a : α} :
    (a ::ᵥ as).mapM f = return (← f a) ::ᵥ (← as.mapM f) := by
  rcases as with ⟨as, rfl⟩
  rfl

lemma toList_mapM {m} [Monad m] [LawfulMonad m] (f : α → m β) (as : Vector α n) :
    toList <$> as.mapM f = as.toList.mapM f := by
  induction as with
  | nil => simp only [toList_empty, List.mapM_nil, mapM_nil, map_pure]
  | @cons n a as ih => simp_all only [← ih, Nat.succ_eq_add_one, length_append, mapM_cons,
    bind_pure_comp, map_bind, Functor.map_map, toList_cons, List.mapM_cons]

end mapM

section mapIdxM

@[inline] def mapIdxM {m} [Monad m] {n : Nat} (f : (i : Nat) → α → m β) (as : List.Vector α n) :
      m <| List.Vector β n :=
  match n, as with
  | 0, ⟨[], _⟩ => pure nil
  | n'+1, ⟨a :: l, h⟩ => return (← f 0 a) ::ᵥ
      (← mapIdxM (n := n') (fun i ↦ f (i+1)) ⟨l, by simp_all⟩)

lemma mapIdxM_nil {m} [Monad m] (f : Nat → α → m β) :
    nil.mapIdxM f = pure nil := by simp [mapIdxM]

lemma mapIdxM_cons {m} [Monad m] {n : Nat} (f : Nat → α → m β) (a : α) (as : Vector α n) :
    (a ::ᵥ as).mapIdxM f = return (← f 0 a) ::ᵥ (← as.mapIdxM fun i ↦ f (i+1)) := by
  rcases as with ⟨as, as_h⟩
  simp [mapIdxM]

end mapIdxM

section ListLemmas
@[simp, grind =] theorem List.mapIdxM_nil {m} [Monad m] {f : Nat → α → m β} :
    [].mapIdxM f = pure [] := rfl

#check List.mapIdxM'
@[simp, grind =] theorem List.mapIdxM_cons {m} [Monad m] {f : Nat → α → m β} (a : α) (l : List α) :
    (a :: l).mapIdxM f = (return (← f 0 a) :: (← l.mapIdxM (fun i ↦ f (i+1)))) := by
  rw [← List.mapIdxM'_eq_mapIdxM]
  simp []


end ListLemmas

section mapFinIdxM

@[inline] def mapFinIdxM {m} [Monad m] {n : Nat} (f : (i : Nat) → α → (i < n) → m β)
    (as : List.Vector α n) : m <| List.Vector β n :=
  match n, as with
  | 0, ⟨[], _⟩ => pure nil
  | n'+1, ⟨a :: l, h⟩ => return (← f 0 a (by omega)) ::ᵥ (← mapFinIdxM (n := n')
      (fun i a inv ↦ f (i+1) a (by simp_all)) ⟨l, by simp_all⟩)

lemma mapFinIdxM_nil {m} [Monad m] (f : (i : Nat) → α → (i < 0) → m β) :
    nil.mapFinIdxM f = pure nil := by simp [mapFinIdxM]

lemma mapFinIdxM_cons {m} [Monad m] {n : Nat} (f : (i : Nat) → α → (i < n + 1) → m β)
      (a : α) (as : Vector α n) :
    (a ::ᵥ as).mapFinIdxM f = return (← f 0 a (by omega)) ::ᵥ
      (← as.mapFinIdxM fun i a h ↦ f (i+1) a (by omega)) := by
  rcases as with ⟨as, as_h⟩
  simp [mapFinIdxM]

lemma mapIdxM_mapFinIdxM {m} [Monad m] {n : Nat} (f : (i : Nat) → α → m β) (as : Vector α n) :
    as.mapIdxM f = as.mapFinIdxM (fun i a _ ↦ f i a) := by
  induction as generalizing f with
  | nil => simp [mapIdxM_nil, mapFinIdxM_nil]
  | cons ih => simp only [Nat.succ_eq_add_one, length_append, mapIdxM_cons, ih, mapFinIdxM_cons]

-- lemma monadMap_pure {m} [Monad m] {α β : Type*} {f : α → β} {a : α} :
--     f <$> (pure a) = pure (f a) := by
--   simp

lemma toList_mapFinIdxM {m} [Monad m] [LawfulMonad m] {n : Nat} (f : (i : Nat) → α → (i < n) → m β) (as : Vector α n) :
    toList <$> as.mapFinIdxM f = as.toList.mapFinIdxM (fun i a h ↦ f i a (by simp_all only [toList_length])) := by
  induction as generalizing f with
  | nil => simp only [mapFinIdxM_nil, map_pure, toList_empty, List.mapFinIdxM, toList_nil,
    length_nil, mapFinIdxM.go]
  | cons ih =>
    expose_names
    simp [mapFinIdxM_cons, List.mapFinIdxM, List.mapFinIdxM.go]
    specialize ih (fun i a h ↦ f (i + 1) a (by omega))

end mapFinIdxM

end List.Vector
