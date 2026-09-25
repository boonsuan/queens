import Queens.Finite.Local

/-!
# Completeness of branching and input extension

Algorithm 1 explores every answer permitted by the history graph. These lemmas
show that a successful calculation retains every prescribed permitted path. They
are structural properties of the total Lean implementation, independent of the
certificate and of the actual queen word. An error in an unrelated branch is
never silently ignored: successful termination remains an explicit hypothesis.
-/

namespace Queens.Finite

/-- If a branching traversal succeeds, each visited input has a successful
result, and every result of that input belongs to the combined output.
This is the no-dropped-branches property used in Lemma 16. -/
theorem allBranches_branch {α β : Type} {xs : List α}
    {f : α → Except Failure (List β)} {out : List β}
    (hok : allBranches xs f = .ok out) {x : α} (hx : x ∈ xs) :
    ∃ ys, f x = .ok ys ∧ ∀ y ∈ ys, y ∈ out := by
  induction xs generalizing out with
  | nil => simp at hx
  | cons a xs ih =>
    cases ha : f a with
    | error e => simp [allBranches, ha, Bind.bind, Except.bind] at hok
    | ok first =>
      cases hs : allBranches xs f with
      | error e => simp [allBranches, ha, hs, Bind.bind, Except.bind] at hok
      | ok rest =>
        have hout : first ++ rest = out := by
          simpa [allBranches, ha, hs, Bind.bind, Except.bind, Pure.pure, Except.pure] using hok
        subst out
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨first, ha, fun y hy => List.mem_append_left _ hy⟩
        · obtain ⟨ys, hys, hall⟩ := ih hs hx
          exact ⟨ys, hys, fun y hy => List.mem_append_right _ (hall y hy)⟩

/-- Definition 11: a finite list of permitted labels starting at a specified
encoded history. The memory parameter also covers the forty-symbol graph used
in Corollary 19. This is a local path, without an assumption about the board. -/
def PermittedPath (graph : HistoryGraph) (vertex : ℕ) (symbols : List ℕ)
    (memory : ℕ := historyLength) : Prop :=
  match symbols with
  | [] => True
  | symbol :: symbols =>
      ∃ answers, graph.answers vertex = some answers ∧ symbol ∈ answers ∧
        PermittedPath graph (destination vertex symbol (memory := memory)) symbols
          (memory := memory)

/-- A successful `Extend` retains any prescribed permitted suffix of the
requested length. This is the operational input-path part of Lemma 16. -/
theorem extendBy_contains_path {memory : ℕ} {graph : HistoryGraph} {input : ℕ}
    {suffix queue : List ℕ} {out : List (List ℕ)}
    (hpath : PermittedPath graph (queue.foldl (destination (memory := memory)) input)
      suffix (memory := memory))
    (hok : extendBy graph input suffix.length queue (memory := memory) = .ok out) :
    queue ++ suffix ∈ out := by
  induction suffix generalizing queue out with
  | nil =>
    have hout : [queue] = out := by simpa [extendBy] using hok
    simp [← hout]
  | cons symbol suffix ih =>
    obtain ⟨answers, hanswers, hsymbol, hpath⟩ := hpath
    cases answers with
    | nil => simp at hsymbol
    | cons a answers =>
      have hbranches : allBranches (a :: answers)
          (fun s => extendBy graph input suffix.length (queue ++ [s]) (memory := memory)) =
          .ok out := by
        simpa [extendBy, hanswers, Bind.bind, Except.bind] using hok
      obtain ⟨outputs, houtputs, hall⟩ := allBranches_branch hbranches hsymbol
      have hpath' : PermittedPath graph
          ((queue ++ [symbol]).foldl (destination (memory := memory)) input) suffix
          (memory := memory) := by
        simpa [List.foldl_append] using hpath
      have hmem := hall _ (ih hpath' houtputs)
      simpa [List.append_assoc] using hmem

/-- A successful complete calculation has successful preliminary extension,
candidate traversal, and finishing traversal. This exposes the three stages of
Algorithm 1 for the semantic correspondence proof. -/
theorem calculate_decompose {memory : ℕ} {graph : HistoryGraph} {s : State} {out : List State}
    (hok : calculate graph s (memory := memory) = .ok out) :
    ∃ queues choices,
      extendQueue graph s.input s.queue s.z (memory := memory) = .ok queues ∧
      allBranches queues (fun queue =>
        chooseFrom graph s (s.w + 1).toNat 0 queue (memory := memory)) = .ok choices ∧
      allBranches choices (finishChoice graph s (memory := memory)) = .ok out := by
  cases hextend : extendQueue graph s.input s.queue s.z (memory := memory) with
  | error e => simp [calculate, hextend, Bind.bind, Except.bind] at hok
  | ok queues =>
    cases hchoose : allBranches queues
        (fun queue => chooseFrom graph s (s.w + 1).toNat 0 queue (memory := memory)) with
    | error e => simp [calculate, hextend, hchoose, Bind.bind, Except.bind] at hok
    | ok choices =>
      refine ⟨queues, choices, rfl, hchoose, ?_⟩
      simpa [calculate, hextend, hchoose, Bind.bind, Except.bind] using hok

end Queens.Finite
