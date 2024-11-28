# Isabelle Proof Component Graveyard

Just somewhere to keep all the proof components and things that I attempted to use, or wrote, but didn't end up working.



## Task 6

### `simp_measure` definitions

```isabelle
(* original with two inputs *)
function simp_measure :: "query ⇒ valuation option ⇒ nat"
  where
    "simp_measure (q :: query)  v = (
    case v of
      None ⇒ 0
    | Some arr ⇒ (length q) - (length arr))"
   apply auto[1] by blast
```

### `simp_solve` termination proof components

```isabelle
then have "((update_clause x bv ((x, b) # c)) @ q) = update_query x bv q ⟹ x ∉ (symbols q)"

then have "simp_measure ((update_clause x bv ((x, b) # c)) @ q) = simp_measure (update_query x bv (((x, b) # c) # q)) ⟹ x ∉ (symbols q)"

then have "simp_measure [c] = simp_measure_c c" by simp

then have uc_lt_c: "simp_measure (update_clause x bv ((x, b) # c)) < simp_measure [((x, b) # c)]"
  using update_clause_def by (simp add: member_rec(1)) (* have proved breakdown of LHS *)
(* TODO: break down RHS, then compare their constituent parts *)
also have "... ≤ simp_measure (((x, b) # c) # q)" using thesis_split uq_eq_uc try

then have uq_eq_uc: "simp_measure (update_query x b [((x, b) # c)]) = simp_measure (update_clause x bv ((x, b) # c))"
  by (simp add: b_case)


then have "simp_measure (update_query x bv q) < simp_measure q ⟹ x ∈ symbols q"
  using symbol_in_symbol_query symbol_in_symbol_clause try
then have "((update_clause x bv ((x, b) # c)) @ q) = update_query x bv q ⟹ x ∉ (symbols q)"
  using symbol_in_symbol_query symbol_in_symbol_clause try
then have "simp_measure ((update_clause x bv ((x, b) # c)) @ q) < simp_measure (((x, b) # c) # q)"

  using simp_measure.simps simp_measure_c.simps member_def try
then have "simp_measure (update_query x bv q) ≤ simp_measure q"



  proof (cases "x ∈ (symbols q)")
    case True
    then have "x ∈ (symbols_clause c) ⟹ x ∈ (symbols q)" by simp
    then have "(in_query (x, b) q) ∨ (in_query (x, ¬b) q)" try

"simp_measure (update_query (x ::symbol) True (((x, b) # c) # q)) < simp_measure (((x, b) # c) # q)"
   next
    case False
    then show ?thesis sorry
  qed
next
  fix x b c q
  show "simp_measure (update_query x False (((x, b) # c) # q)) < simp_measure (((x, b) # c) # q)"
    sorry
qed
```

### `simp_solve` termination proof

This one apparently didn't prove any subgoals because I used `bv` as a stand-in for `True` and `False`, which it apparently didn't like...

```isabelle
termination
proof (relation "measure simp_measure"; clarify; simp_all del: update_query.simps simp_measure.simps)
  fix x b c q bv
  show "simp_measure (update_query (x :: symbol) (bv :: bool) (((x, b) # c) # q)) < simp_measure (((x, b) # c) # q)"
  proof (cases "bv = b")
    case b_case: True
    then have thesis_split: "simp_measure (update_query x b (((x, b) # c) # q)) = simp_measure (update_clause x b ((x, b) # c)) + simp_measure (update_query x b q)"
      by simp
    also have "... = simp_measure (update_clause x bv ((x, b) # c)) + simp_measure (update_query x b q)"
      by (simp add: b_case)
    also have " simp_measure (update_clause x bv ((x, b) # c)) + simp_measure (update_query x b q) < simp_measure [((x, b) # c)] + simp_measure (update_query x b q)"
      by (simp add: b_case member_def update_clause_def)
    also have "... ≤ simp_measure [((x, b) # c)] + simp_measure q " using uq_le_q
      by simp
    also have "... = simp_measure (((x, b) # c) # q)"  by simp
    finally show ?thesis
      using b_case by fastforce
  next
    case b_case: False
    then have "simp_measure (update_query x bv (((x, b) # c) # q)) = simp_measure (update_clause x bv ((x, b) # c)) + simp_measure (update_query x bv q)"
      by simp
    also have "simp_measure (update_clause x bv ((x, b) # c)) + simp_measure (update_query x bv q) < simp_measure [(x, b) # c] + simp_measure (update_query x bv q)"
      using uc_lt_c_w_xb by auto
    also have "... ≤ simp_measure [((x, b) # c)] + simp_measure q " using uq_le_q
      by simp
    also have "... = simp_measure (((x, b) # c) # q)"  by simp
    finally show ?thesis
      by blast
  qed
```