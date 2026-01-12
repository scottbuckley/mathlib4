/-
Copyright (c) 2026 Scott Buckley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Buckley
-/
module

public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Vector.Basic
import Mathlib.Tactic

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` vars.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

/-!
  This file adds a number of missing definitions and lemmas to the `Vector` API.
-/

namespace List.Vector

variable {α β : Type*} {n m k : ℕ}

section Generic

abbrev singleton (a : α) : Vector α 1 := a ::ᵥ nil

lemma cons_eq_cons {a b : α} {as bs : Vector α n} :
    a = b → as = bs → a ::ᵥ as = b ::ᵥ bs := by
  intros h1 h2
  simp [h1, h2]

@[simp] lemma ofFn_zero {α : Type*} {f : Fin 0 → α} : ofFn f = nil := rfl

lemma Fin.plus_one_succ {n : Nat} (i : Nat) (h : i + 1 < n + 1) :
    Fin.mk (i + 1) h = (Fin.mk (n := n) i (by omega)).succ := rfl

end Generic

section Cast
/- Helper for casting between (equivalent) `Vector` lengths.
Since it's unavoidable to occasionally use cast when working with Vectors,
this at least does it in a way that hides away the cast in a propositional
value. I've made it a rule never to add to `simp` anything that *introduces*
`cast`, but i've added plenty of rules to simp that push `cast` further
to the "outside" of an expression. -/

/-- Creates a vector from another with a provably equal length. -/
@[inline, expose] protected def cast (h : n = m) (as : Vector α n) : Vector α m :=
  ⟨as.toList, by simp only [toList_length, h]⟩

@[simp] lemma cast_refl {n : Nat} (as : Vector α n) :
    (as.cast rfl) = as := rfl

@[simp] theorem cast_mk {as : List α} {h : as.length = n} {h' : n = m} :
    cast h' ⟨as, h⟩ = ⟨as, (by simp only [h, h'])⟩ := rfl

@[simp] lemma cast_cast (h1 : m = n) (h2 : n = k) (as : Vector α m) :
    (as.cast h1).cast h2 = as.cast (by simp_all only) := rfl

@[simp] lemma cast_cons (h : n = m) (a : α) (as : Vector α n) :
    a ::ᵥ (as.cast h) = (a ::ᵥ as).cast (by omega) := rfl

@[simp] lemma cast_map (as : Vector α n) (f : α → β) {h : n = m} :
    (as.cast h).map f = (as.map f).cast h := by rfl

@[simp] lemma cast_f (f : {k : Nat} → Vector α k → Vector β k) (as : Vector α n) {h : n = m} :
    f (as.cast h) = (f as).cast h := by cases h ; rfl

@[simp] lemma cast_append_left (h : n = k) (as : Vector α n) (bs : Vector α m) :
    as.cast h ++ bs = (as ++ bs).cast (by omega) := rfl

@[simp] lemma cast_append_right (h : m = k) (as : Vector α n) (bs : Vector α m) :
    as ++ bs.cast h = (as ++ bs).cast (by omega) := rfl

lemma cast_eq_symm {h : m = n} {as : Vector α n} {bs : Vector α m} (hc : as = bs.cast h) :
    bs = as.cast (by simp_all only) := by simp_all only [cast_cast, cast_refl]

-- lemma cast_right {n m : Nat} {h : n = m} {as : Vector α n} {bs : Vector α m} :
--     as.cast h = bs → as = bs.cast (Eq.symm h) := by
--   intros h2
--   simp only [Eq.symm h2, cast_cast, cast_refl]

end Cast

section Append

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
  simp [append_def, List.append_assoc, cast_mk]

lemma append_assoc.symm (as : Vector α n) (bs : Vector α m) (cs : Vector α k) :
    (as ++ bs ++ cs) = (as ++ (bs ++ cs)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  rcases cs with ⟨cs, rfl⟩
  simp [append_def, List.append_assoc, cast_mk]

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
    simp only [length_append, Nat.reduceAdd, ofFn_zero, Fin.last_zero, Fin.isValue]
    rw [nil_append]
    simp only [ofFn_succ, Fin.isValue, ofFn_zero, length_append, Nat.reduceAdd, cast_refl]
  | succ n ih =>
    rw [ofFn_succ]
    conv => rhs; rw [ofFn_succ]
    rw [ih]
    simp only [length_append, Fin.succ_last, Nat.succ_eq_add_one, Fin.castSucc_zero,
      Fin.castSucc_succ]
    rfl

end ofFn

section Range

def range (n : Nat) : Vector Nat n :=
  loop n nil (zero_add n)
where
  loop {m : Nat} : (k : Nat) → Vector Nat m → (inv : m+k=n) → Vector Nat n
  | 0,   acc, h => acc.cast <| by omega
  | z+1, acc, h => loop z (z ::ᵥ acc) <| by omega

@[simp] lemma range_zero :
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
    simp only [length_append, range'_zero, mul_zero, add_zero, nil_append]
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
    range 1 = singleton 0 := by simp only [range, range.loop, Nat.succ_eq_add_one, length_append,
      Nat.reduceAdd, cast_refl]

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
    range n = ofFn (fun i : Fin n ↦ i.1) := by
  induction n
  next => simp only [range_zero, ofFn_zero]
  next n' ih =>
    rw [range_succ, ih, ofFn_succ_last]
    simp only [length_append, Fin.val_castSucc, Fin.val_last]

end Range

section MapIdx

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
    as.mapIdx f = ⟨as.1.mapIdx f, by simp [*, length_mapIdx]⟩ := by
  induction as generalizing f
  · rfl
  · expose_names
    simp only [Nat.succ_eq_add_one, length_append, mapIdx_cons, cons_val, List.mapIdx_cons]
    specialize h (fun i ↦ f (i+1))
    rw [←cons] <;> simp_all

@[grind =]
theorem mapIdx_append {as : Vector α n} {bs : Vector α m} :
    (as ++ bs).mapIdx f = as.mapIdx f ++ bs.mapIdx fun i => f (i + n) := by
  rcases as with ⟨as, as_h⟩
  rcases bs with ⟨bs, bs_h⟩
  simp only [mapIdx_eq_List_mapIdx, append_def, List.mapIdx_append, as_h]

@[simp, grind =] theorem mapIdx_concat {as : Vector α n} {a : α} :
    (as ++ singleton a).mapIdx f = as.mapIdx f ++ singleton (f n a) := by
  simp only [length_append, mapIdx_append, mapIdx_cons, zero_add, mapIdx_nil]

theorem mapIdx_singleton {a : α} : mapIdx f (singleton a) = singleton (f 0 a) := by
  simp only [mapIdx_cons, length_append, mapIdx_nil]

@[simp, grind =] theorem mapIdx_mapIdx {γ : Type*} {as : Vector α n}
    {f : Nat → α → β} {g : Nat → β → γ} :
    (as.mapIdx f).mapIdx g = as.mapIdx (fun i => g i ∘ f i) := by
  simp only [mapIdx_eq_List_mapIdx, List.mapIdx_mapIdx]

@[simp] lemma cast_mapIdx (as : Vector α n) (f : Nat → α → β) {h : n = m} :
    (as.cast h).mapIdx f = (as.mapIdx f).cast h := by
  rcases as with ⟨as, as_h⟩
  simp only [mapIdx_eq_List_mapIdx]

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
    next i' => rw [Fin.plus_one_succ, get_cons_succ, get_cons_succ, i_h, Fin.succ_mk]

lemma mapIdx_id (as : Vector α n) :
    as.mapIdx (fun _ a ↦ a) = as := by
  induction as
  · rfl
  · expose_names
    simp only [Nat.succ_eq_add_one, length_append, mapIdx_cons, h]

lemma mapIdx_idx (as : Vector α n) :
    as.mapIdx (fun i _ ↦ i) = range n := by


end MapIdx




end Vector
