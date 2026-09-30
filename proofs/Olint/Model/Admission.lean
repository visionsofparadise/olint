import Olint.Model.Cost

/-!
# Admission is non-empty

`Admitted.exists`: every well-formed entry (`Entry.wf`) admits an instance at every valuation
of its dimensions by natural numbers, so a bound over it (`Olint.Bound`) constrains the entry's
runs at every size and never holds vacuously.

The witness heap holds four shared objects, then one object per argument and free variable, then
the free variables' binding cells:

* location `0`: an ordinary object whose accessors are every field name the entry's declared
  types mention, so it conforms to every object type among them (§2.5 admits an accessor for a
  field, `Olint.Model.conforms`);
* locations `1` to `3`: an empty Array, Map and Set, which conform to every Array, Map and Set
  type;
* per argument and free variable, a value of the declared type measuring the length its
  dimension asks for: `n` copies of a conforming element for an Array (and for `any`), `n`
  deleted records for a Map or Set, whose `|D|` counts them (`Olint.Model.Heap.lengthOf`), and
  `n` code units for a String.
-/

namespace Olint.Model

/-! ## Witness values -/

mutual

/-- The field names a declared type mentions, at any depth. -/
def Ty.names : Ty → List Name
  | .array τ | .set τ => Ty.names τ
  | .map κ τ => Ty.names κ ++ Ty.names τ
  | .object fs => fs.map Prod.fst ++ Ty.namesFields fs
  | _ => []

/-- `Ty.names` over object type fields. -/
def Ty.namesFields : List (Name × Ty) → List Name
  | [] => []
  | (_, τ) :: fs => Ty.names τ ++ Ty.namesFields fs

end

/-- A value of each declared type in the witness heap. -/
def inhab : Ty → Value
  | .any | .undefined => .undef
  | .null => .null
  | .boolean => .bool false
  | .number => .num 0
  | .string => .str ""
  | .func => .builtin .mapGet
  | .object _ => .ref 0
  | .array _ => .ref 1
  | .map _ _ => .ref 2
  | .set _ => .ref 3

/-- The shared objects at locations `0` to `3`. -/
def baseObjs (N : List Name) : List Obj :=
  [.ordinary [] N none, .array [], .map [], .set []]

/-- The object measuring `n` that a slot of declared type `τ` refers to. -/
def slotObj : Ty → ℕ → Obj
  | .array σ, n => .array (List.replicate n (inhab σ))
  | .map _ _, n => .map (List.replicate n none)
  | .set _, n => .set (List.replicate n none)
  | .any, n => .array (List.replicate n .undef)
  | _, _ => .array []

/-- The value of a slot of declared type `τ` measuring `n`, its object at location `l`. -/
def slotVal (l : Loc) (τ : Ty) (n : ℕ) : Value :=
  match τ with
  | .string => .str (String.ofList (List.replicate n 'a'))
  | .array _ | .map _ _ | .set _ | .any => .ref l
  | τ => inhab τ

/-- The length a dimension over measure `m` takes: that of the first dimension measuring it. -/
def lenFor (ds : List (ℕ × Measure)) (d : ℕ → ℕ) (m : Measure) : ℕ :=
  match ds.find? (fun x => x.2 == m) with
  | some x => d x.1
  | none => 0

/-- The arguments' slot objects, the `k`-th parameter first. -/
def argObjs (len : Measure → ℕ) : ℕ → List (Name × Ty) → List Obj
  | _, [] => []
  | k, (_, τ) :: ps => slotObj τ (len (.arg k)) :: argObjs len (k + 1) ps

/-- The arguments, the `k`-th parameter first. -/
def argVals (len : Measure → ℕ) : ℕ → List (Name × Ty) → List Value
  | _, [] => []
  | k, (_, τ) :: ps => slotVal (4 + k) τ (len (.arg k)) :: argVals len (k + 1) ps

/-- The free variables' slot objects. -/
def varObjs (len : Measure → ℕ) : List (Name × Ty) → List Obj
  | [] => []
  | (x, τ) :: ss => slotObj τ (len (.var x)) :: varObjs len ss

/-- The free variables' binding cells, their slot objects from location `B + j` on. -/
def varCells (len : Measure → ℕ) (B : ℕ) : ℕ → List (Name × Ty) → List Obj
  | _, [] => []
  | j, (x, τ) :: ss => .cell (slotVal (B + j) τ (len (.var x))) τ :: varCells len B (j + 1) ss

/-- The environment binding the free variables to their cells, from location `C + j` on. -/
def envOf (C : ℕ) : ℕ → List (Name × Ty) → Env
  | _, [] => []
  | j, (x, _) :: ss => (x, C + j) :: envOf C (j + 1) ss

/-- A heap holding a list of objects at locations `0, 1, …`. -/
def Heap.ofList (objs : List Obj) : Heap := ⟨objs.length, fun l => objs[l]?⟩

/-! ## List lemmas -/

theorem argObjs_length (len : Measure → ℕ) :
    ∀ k (ps : List (Name × Ty)), (argObjs len k ps).length = ps.length
  | _, [] => rfl
  | k, _ :: ps => by simp [argObjs, argObjs_length len (k + 1) ps]

theorem varObjs_length (len : Measure → ℕ) :
    ∀ ss : List (Name × Ty), (varObjs len ss).length = ss.length
  | [] => rfl
  | _ :: ss => by simp [varObjs, varObjs_length len ss]

theorem argObjs_get (len : Measure → ℕ) : ∀ k (ps : List (Name × Ty)) (i : ℕ),
    (argObjs len k ps)[i]? = ps[i]?.map fun q => slotObj q.2 (len (.arg (k + i)))
  | _, [], _ => rfl
  | k, (_, τ) :: ps, 0 => rfl
  | k, (_, τ) :: ps, i + 1 => by
    simp only [argObjs, List.getElem?_cons_succ, argObjs_get len (k + 1) ps i]
    congr 2; funext q; congr 3; omega

theorem argVals_get (len : Measure → ℕ) : ∀ k (ps : List (Name × Ty)) (i : ℕ),
    (argVals len k ps)[i]? = ps[i]?.map fun q => slotVal (4 + k + i) q.2 (len (.arg (k + i)))
  | _, [], _ => rfl
  | k, (_, τ) :: ps, 0 => rfl
  | k, (_, τ) :: ps, i + 1 => by
    simp only [argVals, List.getElem?_cons_succ, argVals_get len (k + 1) ps i]
    rw [show 4 + (k + 1) + i = 4 + k + (i + 1) by omega, show k + 1 + i = k + (i + 1) by omega]

theorem varObjs_get (len : Measure → ℕ) : ∀ (ss : List (Name × Ty)) (i : ℕ),
    (varObjs len ss)[i]? = ss[i]?.map fun q => slotObj q.2 (len (.var q.1))
  | [], _ => rfl
  | (_, τ) :: ss, 0 => rfl
  | (_, τ) :: ss, i + 1 => by simp only [varObjs, List.getElem?_cons_succ, varObjs_get len ss i]

theorem varCells_get (len : Measure → ℕ) (B : ℕ) : ∀ j (ss : List (Name × Ty)) (i : ℕ),
    (varCells len B j ss)[i]? =
      ss[i]?.map fun q => .cell (slotVal (B + (j + i)) q.2 (len (.var q.1))) q.2
  | _, [], _ => rfl
  | j, (_, τ) :: ss, 0 => rfl
  | j, (_, τ) :: ss, i + 1 => by
    simp only [varCells, List.getElem?_cons_succ, varCells_get len B (j + 1) ss i]
    congr 2; funext q; congr 3; omega

theorem arg0_drop : ∀ (l : List Value) (k : ℕ), arg0 (l.drop k) = (l[k]?).getD .undef
  | [], _ => by simp [arg0]
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => arg0_drop l k

theorem find_of_distinct : ∀ (ds : List (ℕ × Measure)) (j : ℕ) (m : Measure),
    distinct (ds.map (·.2)) = true → (j, m) ∈ ds → ds.find? (fun x => x.2 == m) = some (j, m)
  | [], _, _, _, h => absurd h (by simp)
  | (j', m') :: ds, j, m, hd, h => by
    simp only [List.map_cons, distinct, Bool.and_eq_true, Bool.not_eq_true'] at hd
    rcases List.mem_cons.1 h with h | h
    · cases h; simp
    · have hm : m' ≠ m := by
        rintro rfl
        have h1 : (ds.map (·.2)).contains m' = true :=
          List.contains_iff_mem.2 (List.mem_map.2 ⟨(j, m'), h, rfl⟩)
        rw [hd.1] at h1
        exact Bool.false_ne_true h1
      simp only [List.find?_cons, beq_false_of_ne hm]
      exact find_of_distinct ds j m hd.2 h

theorem lenFor_eq {ds : List (ℕ × Measure)} {j : ℕ} {m : Measure} (d : ℕ → ℕ)
    (hd : distinct (ds.map (·.2)) = true) (h : (j, m) ∈ ds) : lenFor ds d m = d j := by
  simp [lenFor, find_of_distinct ds j m hd h]

theorem lookup_mem {β : Type} : ∀ (l : List (Name × β)) (x : Name) (b : β),
    l.lookup x = some b → (x, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (y, c) :: l, x, b, h => by
    by_cases hxy : x = y
    · subst hxy; simp [List.lookup] at h; simp [h]
    · simp only [List.lookup, beq_false_of_ne hxy] at h
      exact List.mem_cons_of_mem _ (lookup_mem l x b h)

theorem envOf_lookup (C : ℕ) : ∀ (ss : List (Name × Ty)) (j : ℕ) (x : Name) (τ : Ty),
    distinctNames (ss.map Prod.fst) = true → (x, τ) ∈ ss →
      ∃ i, (envOf C j ss).lookup x = some (C + (j + i)) ∧ ss[i]? = some (x, τ)
  | [], _, _, _, _, h => absurd h (by simp)
  | (y, σ) :: ss, j, x, τ, hd, h => by
    simp only [List.map_cons, distinctNames, Bool.and_eq_true, Bool.not_eq_true'] at hd
    rcases List.mem_cons.1 h with hm | hm
    · cases hm; exact ⟨0, by simp [envOf], rfl⟩
    · have hxy : x ≠ y := by
        rintro rfl
        have h1 : (ss.map Prod.fst).contains x = true :=
          List.contains_iff_mem.2 (List.mem_map.2 ⟨(x, τ), hm, rfl⟩)
        rw [hd.1] at h1
        exact Bool.false_ne_true h1
      obtain ⟨i, hl, hi⟩ := envOf_lookup C ss (j + 1) x τ hd.2 hm
      refine ⟨i + 1, ?_, by simpa using hi⟩
      rw [show j + (i + 1) = j + 1 + i by omega]
      simpa [envOf, List.lookup, beq_false_of_ne hxy] using hl

theorem envOf_mem (C : ℕ) : ∀ (ss : List (Name × Ty)) (j : ℕ) (x : Name) (l : Loc),
    (x, l) ∈ envOf C j ss → ∃ τ, (x, τ) ∈ ss
  | [], _, _, _, h => absurd h (by simp [envOf])
  | (y, σ) :: ss, j, x, l, h => by
    simp only [envOf, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩ | h
    · exact ⟨σ, List.mem_cons_self⟩
    · obtain ⟨τ, hτ⟩ := envOf_mem C ss (j + 1) x l h
      exact ⟨τ, List.mem_cons_of_mem _ hτ⟩

theorem utf16Length_replicate (n : ℕ) : utf16Length (String.ofList (List.replicate n 'a')) = n := by
  unfold utf16Length
  rw [String.toList_ofList]
  have : ∀ (m a : ℕ), (List.replicate m 'a').foldl
      (fun n c => n + if 0xFFFF < c.toNat then 2 else 1) a = a + m := by
    intro m
    induction m with
    | zero => intro a; rfl
    | succ m ih =>
      intro a
      rw [List.replicate_succ, List.foldl_cons, ih]
      have : ¬ (0xFFFF < 'a'.toNat) := by decide
      simp only [this, ↓reduceIte]
      omega
  simpa using this n 0

/-! ## The witness heap -/

section Witness

variable (N : List Name) (len : Measure → ℕ) (ps ss : List (Name × Ty))

/-- The objects that are no binding cell: the shared objects and the slot objects. -/
def prefixObjs : List Obj := baseObjs N ++ argObjs len 0 ps ++ varObjs len ss

/-- The witness heap. -/
def witness : Heap :=
  Heap.ofList (prefixObjs N len ps ss ++ varCells len (4 + ps.length) 0 ss)

theorem prefixObjs_length : (prefixObjs N len ps ss).length = 4 + ps.length + ss.length := by
  simp [prefixObjs, baseObjs, argObjs_length, varObjs_length]
  omega

theorem slotObj_isValue (τ : Ty) (n : ℕ) : (slotObj τ n).isValue = true := by
  cases τ <;> rfl

theorem prefixObjs_isValue : ∀ o ∈ prefixObjs N len ps ss, o.isValue = true := by
  intro o ho
  simp only [prefixObjs, List.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · simp only [baseObjs, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> rfl
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem ho
    rw [argObjs_get] at hi
    obtain ⟨q, _, rfl⟩ := Option.map_eq_some_iff.1 hi
    exact slotObj_isValue _ _
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem ho
    rw [varObjs_get] at hi
    obtain ⟨q, _, rfl⟩ := Option.map_eq_some_iff.1 hi
    exact slotObj_isValue _ _

theorem witness_get_prefix {l : ℕ} (hl : l < 4 + ps.length + ss.length) :
    (witness N len ps ss).get l = (prefixObjs N len ps ss)[l]? := by
  simp only [witness, Heap.ofList]
  rw [List.getElem?_append_left (by rw [prefixObjs_length]; exact hl)]

theorem witness_get_base (l : ℕ) (hl : l < 4) :
    (witness N len ps ss).get l = (baseObjs N)[l]? := by
  rw [witness_get_prefix N len ps ss (by omega), prefixObjs, List.append_assoc,
    List.getElem?_append_left (by simp [baseObjs]; exact hl)]

theorem witness_get_arg (k : ℕ) (hk : k < ps.length) :
    (witness N len ps ss).get (4 + k) = ps[k]?.map fun q => slotObj q.2 (len (.arg k)) := by
  rw [witness_get_prefix N len ps ss (by omega), prefixObjs,
    List.getElem?_append_left (by simp [baseObjs, argObjs_length]; omega),
    List.getElem?_append_right (by simp [baseObjs])]
  simp [baseObjs, argObjs_get]

theorem witness_get_var (j : ℕ) (hj : j < ss.length) :
    (witness N len ps ss).get (4 + ps.length + j) =
      ss[j]?.map fun q => slotObj q.2 (len (.var q.1)) := by
  have hlen : (baseObjs N ++ argObjs len 0 ps).length = 4 + ps.length := by
    simp [baseObjs, argObjs_length]; omega
  rw [witness_get_prefix N len ps ss (by omega), prefixObjs,
    List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show 4 + ps.length + j - (4 + ps.length) = j by omega, varObjs_get]

theorem witness_get_cell (j : ℕ) :
    (witness N len ps ss).get (4 + ps.length + ss.length + j) =
      ss[j]?.map fun q => .cell (slotVal (4 + ps.length + j) q.2 (len (.var q.1))) q.2 := by
  simp only [witness, Heap.ofList]
  rw [List.getElem?_append_right (by rw [prefixObjs_length]; omega), prefixObjs_length,
    varCells_get]
  simp

theorem witness_valueOk_ref {l : ℕ} (hl : l < 4 + ps.length + ss.length) :
    (witness N len ps ss).valueOk (.ref l) = true := by
  have hl' : l < (prefixObjs N len ps ss).length := by rw [prefixObjs_length]; exact hl
  simp only [Heap.valueOk, witness_get_prefix N len ps ss hl, List.getElem?_eq_getElem hl']
  exact prefixObjs_isValue N len ps ss _ (List.getElem_mem hl')

theorem witness_valueOk_inhab (τ : Ty) : (witness N len ps ss).valueOk (inhab τ) = true := by
  cases τ <;> rfl

theorem witness_valueOk_slot {l : ℕ} (hl : l < 4 + ps.length + ss.length) (τ : Ty) (n : ℕ) :
    (witness N len ps ss).valueOk (slotVal l τ n) = true := by
  cases τ <;> first
    | rfl
    | exact witness_valueOk_ref N len ps ss hl

theorem witness_WF : (witness N len ps ss).WF := fun l hl => by
  simp only [witness, Heap.ofList] at hl ⊢
  exact List.getElem?_eq_none hl

theorem witness_closed : (witness N len ps ss).Closed := by
  intro l o hget
  have hmem : o ∈ prefixObjs N len ps ss ++ varCells len (4 + ps.length) 0 ss :=
    List.mem_of_getElem? hget
  rcases List.mem_append.1 hmem with ho | ho
  · simp only [prefixObjs, List.mem_append] at ho
    rcases ho with (ho | ho) | ho
    · simp only [baseObjs, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> rfl
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem ho
      rw [argObjs_get] at hi
      obtain ⟨q, _, rfl⟩ := Option.map_eq_some_iff.1 hi
      rcases q with ⟨_, τ⟩
      cases τ <;> simp [slotObj, Heap.objOk, witness_valueOk_inhab,
        show (witness N len ps ss).valueOk .undef = true from rfl]
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem ho
      rw [varObjs_get] at hi
      obtain ⟨q, _, rfl⟩ := Option.map_eq_some_iff.1 hi
      rcases q with ⟨_, τ⟩
      cases τ <;> simp [slotObj, Heap.objOk, witness_valueOk_inhab,
        show (witness N len ps ss).valueOk .undef = true from rfl]
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem ho
    rw [varCells_get] at hi
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hi
    have hi' : i < ss.length := (List.getElem?_eq_some_iff.1 hq).1
    simp only [Heap.objOk]
    exact witness_valueOk_slot N len ps ss (by omega) _ _

/-! ## Conformance of the witness values -/

theorem witness_fieldView (x : Name) (hx : x ∈ N) :
    fieldView (witness N len ps ss) (.ref 0) x = .present := by
  simp [fieldView, witness_get_base N len ps ss 0 (by omega), baseObjs, List.lookup, hx]

theorem witness_conformsFields : ∀ fs : List (Name × Ty), (∀ x ∈ fs.map Prod.fst, x ∈ N) →
    conformsFields (witness N len ps ss) (.ref 0) fs = true
  | [], _ => by simp [conformsFields]
  | (x, τ) :: fs, h => by
    simp only [conformsFields, witness_fieldView N len ps ss x (h x (by simp)), Bool.true_and]
    exact witness_conformsFields fs fun y hy => h y (by simp [hy])

theorem witness_inhab (τ : Ty) (hN : ∀ x ∈ τ.names, x ∈ N) :
    conforms (witness N len ps ss) (inhab τ) τ = true := by
  cases τ with
  | object fs =>
    simp only [inhab, conforms]
    exact witness_conformsFields N len ps ss fs fun x hx => hN x (by simp [Ty.names, hx])
  | array σ => simp [inhab, conforms, witness_get_base N len ps ss 1 (by omega), baseObjs]
  | map κ σ => simp [inhab, conforms, witness_get_base N len ps ss 2 (by omega), baseObjs]
  | set σ => simp [inhab, conforms, witness_get_base N len ps ss 3 (by omega), baseObjs]
  | _ => rfl

/-- A slot value conforms to its type, and a measurable one has the length its slot asks for. -/
theorem witness_slot {l : ℕ} (τ : Ty) (n : ℕ) (hN : ∀ x ∈ τ.names, x ∈ N)
    (hl : (witness N len ps ss).get l = some (slotObj τ n)) :
    conforms (witness N len ps ss) (slotVal l τ n) τ = true ∧
      (τ.measurable = true → (witness N len ps ss).lengthOf (slotVal l τ n) = some n) := by
  cases τ with
  | any => exact ⟨rfl, fun _ => by simp [slotVal, Heap.lengthOf, hl, slotObj]⟩
  | string => exact ⟨rfl, fun _ => by simp [slotVal, Heap.lengthOf, utf16Length_replicate]⟩
  | array σ =>
    refine ⟨?_, fun _ => by simp [slotVal, Heap.lengthOf, hl, slotObj]⟩
    simp only [slotVal, conforms, hl, slotObj, List.all_eq_true, List.mem_replicate]
    rintro w ⟨_, rfl⟩
    exact witness_inhab N len ps ss σ fun x hx => hN x (by simpa [Ty.names] using hx)
  | map κ σ =>
    refine ⟨?_, fun _ => by simp [slotVal, Heap.lengthOf, hl, slotObj]⟩
    simp only [slotVal, conforms, hl, slotObj, List.all_eq_true, List.mem_replicate]
    rintro w ⟨_, rfl⟩
    rfl
  | set σ =>
    refine ⟨?_, fun _ => by simp [slotVal, Heap.lengthOf, hl, slotObj]⟩
    simp only [slotVal, conforms, hl, slotObj, List.all_eq_true, List.mem_replicate]
    rintro w ⟨_, rfl⟩
    rfl
  | object fs =>
    exact ⟨witness_inhab N len ps ss (.object fs) hN, fun h => by simp [Ty.measurable] at h⟩
  | undefined | null | boolean | number | func =>
    exact ⟨witness_inhab N len ps ss _ hN, fun h => by simp [Ty.measurable] at h⟩

end Witness

/-! ## Admission -/

/-- Every field name the declared types of an entry's parameters and free variables mention. -/
def Entry.names (e : Entry) : List Name :=
  match e.fn with
  | .mk params _ _ => (params.map Prod.snd ++ e.scope.map Prod.snd).flatMap Ty.names

/-- Every well-formed entry admits an instance at every valuation of its dimensions by natural
numbers, so no bound over a well-formed entry holds vacuously. -/
theorem Admitted.exists (p : Program) (e : Entry) (hwf : e.wf p = true) (d : ℕ → ℕ) :
    ∃ i, Admitted e i ∧ ∀ j, i.dims j = d j := by
  obtain ⟨fn, scope, dims⟩ := e
  obtain ⟨params, body, arrow⟩ := fn
  simp only [Entry.wf, Bool.and_eq_true, List.all_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hnames⟩, _⟩, _⟩, hdist⟩, hdims⟩ := hwf
  set e : Entry := ⟨.mk params body arrow, scope, dims⟩ with he
  set N := e.names
  set len := lenFor dims d
  set h := witness N len params scope
  have hNp : ∀ q ∈ params, ∀ x ∈ q.2.names, x ∈ N := fun q hq x hx => by
    simp only [N, Entry.names, he, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨q.2, Or.inl ⟨q, hq, rfl⟩, hx⟩
  have hNs : ∀ q ∈ scope, ∀ x ∈ q.2.names, x ∈ N := fun q hq x hx => by
    simp only [N, Entry.names, he, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨q.2, Or.inr ⟨q, hq, rfl⟩, hx⟩
  -- the `k`-th argument
  have harg : ∀ k x τ, params[k]? = some (x, τ) →
      (argVals len 0 params)[k]? = some (slotVal (4 + k) τ (len (.arg k))) ∧
      conforms h (slotVal (4 + k) τ (len (.arg k))) τ = true ∧
      (τ.measurable = true → h.lengthOf (slotVal (4 + k) τ (len (.arg k))) = some (len (.arg k))) := by
    intro k x τ hk
    have hlt : k < params.length := (List.getElem?_eq_some_iff.1 hk).1
    refine ⟨by simp [argVals_get, hk], witness_slot N len params scope τ _ ?_ ?_⟩
    · exact hNp (x, τ) (List.mem_of_getElem? hk)
    · rw [witness_get_arg N len params scope k hlt, hk]; rfl
  -- the free variable `x`
  have hvar : ∀ x τ, (x, τ) ∈ scope → ∃ j,
      (envOf (4 + params.length + scope.length) 0 scope).lookup x =
        some (4 + params.length + scope.length + j) ∧
      h.get (4 + params.length + scope.length + j) =
        some (.cell (slotVal (4 + params.length + j) τ (len (.var x))) τ) ∧
      conforms h (slotVal (4 + params.length + j) τ (len (.var x))) τ = true ∧
      (τ.measurable = true →
        h.lengthOf (slotVal (4 + params.length + j) τ (len (.var x))) = some (len (.var x))) := by
    intro x τ hx
    obtain ⟨j, hl, hj⟩ := envOf_lookup (4 + params.length + scope.length) scope 0 x τ hnames hx
    have hlt : j < scope.length := (List.getElem?_eq_some_iff.1 hj).1
    refine ⟨j, by simpa using hl, by rw [witness_get_cell, hj]; rfl,
      witness_slot N len params scope τ _ (hNs (x, τ) hx) ?_⟩
    rw [witness_get_var N len params scope j hlt, hj]; rfl
  refine ⟨⟨h, envOf (4 + params.length + scope.length) 0 scope, argVals len 0 params,
    fun j => (d j : ℝ), 0⟩, ?_, fun j => rfl⟩
  refine ⟨witness_WF N len params scope, witness_closed N len params scope, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hv
    rw [argVals_get] at hk
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hk
    have hlt : k < params.length := (List.getElem?_eq_some_iff.1 hq).1
    exact witness_valueOk_slot N len params scope (by omega) _ _
  · intro k x τ hk
    obtain ⟨hget, hc, _⟩ := harg k x τ hk
    show conforms h _ τ = true
    rw [arg0_drop, hget]
    exact hc
  · intro x τ hx
    obtain ⟨j, hl, hc, hconf, _⟩ := hvar x τ hx
    exact ⟨_, _, hl, hc, hconf⟩
  · intro x l hx
    exact envOf_mem _ scope 0 x l hx
  · intro j m hjm
    have hlen : len m = d j := lenFor_eq d hdist hjm
    refine ⟨?_, by simp⟩
    rw [Nat.ceil_natCast]
    have hok := hdims (j, m) hjm
    cases m with
    | arg k =>
      simp only [Entry.dimOk, he] at hok
      split at hok
      · rename_i x τ hk
        obtain ⟨hget, _, hlenk⟩ := harg k x τ hk
        simp only [Instance.measure, hget, Option.bind_some]
        rw [← hlen]
        exact hlenk hok
      · exact absurd hok Bool.false_ne_true
    | var x =>
      simp only [Entry.dimOk, he] at hok
      split at hok
      · rename_i τ hτ
        obtain ⟨j', hl, hc, _, hlenv⟩ := hvar x τ (lookup_mem scope x τ hτ)
        simp only [Instance.measure, Heap.var, hl, hc, Option.bind_some]
        rw [← hlen]
        exact hlenv hok
      · exact absurd hok Bool.false_ne_true

end Olint.Model
