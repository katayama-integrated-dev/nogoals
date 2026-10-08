import NoGoals.IR.Assets
import NoGoals.IR.HtmlVerified
import Mathlib.Data.List.FinRange

/-!
# Navigation Reachability Analysis

**Status: proof showcase.** Real BFS soundness proofs (inductive `Reachable`,
a preserved `BFSInvariant`, fuel induction), consumed by the test suite; the
production pipeline does not run reachability analysis yet, and the site's
verification report does not cite these theorems. Note the caveat: the graph
is extracted by functions that are currently `partial` (unified-plan 3.1), so
soundness is relative to that extraction.

Graph-based analysis to ensure all pages are reachable from the homepage.

## Features

1. **Graph Extraction** - Build adjacency graph from internal links
2. **BFS Traversal** - Find all reachable pages from a starting point
3. **Orphan Detection** - Identify pages with no incoming links
4. **Breadcrumb Validation** - Ensure breadcrumb trails are acyclic
5. **Reachability Theorem** - Prove all pages accessible from home

## Type Safety

- Graph is extracted from verified links (no broken references)
- BFS termination is guaranteed by finite page count
- Orphans are explicitly identified

-/

namespace NoGoals

/-! ## Graph Representation -/

/-- Extract link targets from inline element (total). -/
def extractLinksFromInline {nP nA : Nat} {A : Assets nA} {Anc : Fin nP → List AnchorId} :
    InlineV nP nA A Anc → List (Fin nP)
  | .text _ => []
  | .code _ => []
  | .link target_page _ _ => [target_page]
  | .extlink _ _ => []

/-- Extract link targets from a block (total — the graph BFS soundness is
    proved against is no longer built by an opaque `partial def`). -/
def extractLinksFromBlock {nP nA : Nat} {A : Assets nA} {Anc : Fin nP → List AnchorId} :
    BlockV nP nA A Anc → List (Fin nP)
  | .p inlines => inlines.flatMap extractLinksFromInline
  | .ul items => items.flatMap (·.flatMap extractLinksFromInline)
  | .heading _ _ _ => []
  | .img _ _ => []
  | .section _ blocks => blocks.attach.flatMap (fun ⟨b, _⟩ => extractLinksFromBlock b)

/-- Adjacency list representation of site navigation graph -/
def navGraph {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (source : Fin nP) : List (Fin nP) :=
  let page := S.pages source
  page.body.flatMap extractLinksFromBlock

/-! ## BFS Traversal -/

/-- BFS state -/
structure BFSState (n : Nat) where
  visited : List (Fin n)
  queue : List (Fin n)

/-- Single BFS step -/
def bfsStep {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (state : BFSState nP) : BFSState nP :=
  match state.queue with
  | [] => state  -- Done
  | current :: rest =>
      let neighbors := navGraph S current
      let newNeighbors := neighbors.filter (fun p => !state.visited.contains p)
      { visited := state.visited ++ newNeighbors
        queue := rest ++ newNeighbors }

/-- Run BFS until completion -/
def bfs {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start : Fin nP) (fuel : Nat) : List (Fin nP) :=
  let rec go (state : BFSState nP) (remaining : Nat) : List (Fin nP) :=
    if remaining = 0 then
      state.visited
    else if state.queue.isEmpty then
      state.visited  -- Completed
    else
      go (bfsStep S state) (remaining - 1)
  termination_by remaining
  go { visited := [start], queue := [start] } fuel

/-! ## Reachability -/

/-- Find all pages reachable from start via BFS -/
def reachableFrom {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start : Fin nP) : List (Fin nP) :=
  bfs S start nP  -- At most nP iterations needed

/-- Check if all pages are reachable from home -/
def allPagesReachable {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (home : Fin nP) : Bool :=
  let reachable := reachableFrom S home
  (List.finRange nP).all (fun i => reachable.contains i)

/-! ## Orphan Detection -/

/-- A page is an orphan if no other page links to it -/
def isOrphan {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (target : Fin nP) : Bool :=
  let hasIncomingLink := (List.finRange nP).any fun source =>
    (navGraph S source).contains target
  !hasIncomingLink

/-- Find all orphaned pages (excluding homepage) -/
def findOrphans {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (home : Fin nP) : List (Fin nP) :=
  (List.finRange nP).filter fun i =>
    i ≠ home && isOrphan S i

/-! ## Breadcrumb Validation -/

/-- Check if a path contains a cycle -/
def hasCycle {n : Nat} (path : List (Fin n)) : Bool :=
  let rec go (seen : List (Fin n)) (remaining : List (Fin n)) : Bool :=
    match remaining with
    | [] => false
    | p :: rest =>
        if seen.contains p then true
        else go (p :: seen) rest
  go [] path

/-- Breadcrumb trail representation -/
structure BreadcrumbTrail (n : Nat) where
  path : List (Fin n)
  h_nonempty : path ≠ []

/-- Check if breadcrumb trail is acyclic -/
def breadcrumbAcyclic {n : Nat} (trail : BreadcrumbTrail n) : Bool :=
  !hasCycle trail.path

/-! ## Reachability Theorems -/

/-- If BFS completes and all pages found, then all pages are reachable -/
theorem reachability_complete {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (home : Fin nP)
    (h : allPagesReachable S home = true) :
    ∀ i : Fin nP, i ∈ reachableFrom S home := by
  unfold allPagesReachable at h; aesop

/-! ## BFS Correctness -/

/-- Orphan cannot be a neighbor of any page -/
theorem orphan_not_neighbor {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (page source : Fin nP)
    (h_orphan : isOrphan S page = true) :
    page ∉ navGraph S source := by
  unfold isOrphan at h_orphan
  simp only [Bool.not_eq_true', List.any_eq_false,
             List.contains_iff_mem] at h_orphan
  exact h_orphan source (List.mem_finRange source)

/-- Helper: orphan not in bfsStep output if not already visited -/
private theorem orphan_not_in_bfsStep {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A)
    (state : BFSState nP) (page : Fin nP)
    (h_orphan : isOrphan S page = true)
    (h_not_in : page ∉ state.visited) :
    page ∉ (bfsStep S state).visited := by
  unfold bfsStep
  split
  · exact h_not_in  -- Empty queue: state unchanged
  · -- Non-empty queue: check visited ++ newNeighbors
    rename_i current rest _
    simp only [List.mem_append, List.mem_filter, not_or, not_and]
    exact ⟨h_not_in, fun h_neighbor _ => absurd h_neighbor (orphan_not_neighbor S page current h_orphan)⟩

/-- BFS cannot discover an orphan (page with no incoming links) -/
theorem bfs_go_excludes_orphan {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A)
    (state : BFSState nP) (remaining : Nat) (page : Fin nP)
    (h_orphan : isOrphan S page = true)
    (h_not_in : page ∉ state.visited) :
    page ∉ (bfs.go S state remaining) := by
  induction remaining generalizing state with
  | zero => unfold bfs.go; simp only [↓reduceIte]; exact h_not_in
  | succ m ih =>
    unfold bfs.go
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · exact h_not_in  -- Queue empty: return visited
    · apply ih; exact orphan_not_in_bfsStep S state page h_orphan h_not_in

/-- BFS orphan exclusion: If no page links to a target, BFS cannot discover it. -/
theorem bfs_orphan_excluded {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (home page : Fin nP)
    (h_neq : page ≠ home) (h_orphan : isOrphan S page = true) :
    page ∉ reachableFrom S home := by
  unfold reachableFrom bfs
  apply bfs_go_excludes_orphan S _ nP page h_orphan
  simp only [List.mem_singleton]
  exact h_neq

/-! ## Inductive Reachability -/

/-- Inductive definition of graph reachability.
    A node is reachable if it's the start, or it's a neighbor of a reachable node. -/
inductive Reachable {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start : Fin nP) : Fin nP → Prop where
  | refl : Reachable S start start
  | step (mid target : Fin nP) : Reachable S start mid → target ∈ navGraph S mid → Reachable S start target

/-- Inductive reachability implies path existence -/
theorem reachable_has_path_ind {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start target : Fin nP)
    (h : Reachable S start target) :
    ∃ path : List (Fin nP), path.head? = some start ∧ path.getLast? = some target := by
  induction h with
  | refl => exact ⟨[start], rfl, rfl⟩
  | step mid tgt _ _ ih =>
    obtain ⟨path, h_head, _⟩ := ih
    have h_ne : path ≠ [] := by cases path <;> simp_all
    exact ⟨path ++ [tgt], List.head?_append_of_ne_nil _ h_ne ▸ h_head, List.getLast?_concat ..⟩

/-! ## BFS Soundness: BFS only finds inductively reachable nodes -/

/-- BFS state invariant: all visited nodes are Reachable from start -/
private def BFSInvariant {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start : Fin nP) (state : BFSState nP) : Prop :=
  (∀ p ∈ state.visited, Reachable S start p) ∧
  (∀ p ∈ state.queue, Reachable S start p)

/-- Initial state satisfies invariant -/
private theorem bfs_initial_invariant {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start : Fin nP) :
    BFSInvariant S start { visited := [start], queue := [start] } := by
  constructor <;> (simp only [List.mem_singleton]; intro _ rfl; exact Reachable.refl)

/-- If a new neighbor is in navGraph of a reachable node, it is reachable -/
private theorem neighbor_reachable {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start current p : Fin nP)
    (h_current_reach : Reachable S start current)
    (hp_neighbor : p ∈ navGraph S current) :
    Reachable S start p :=
  Reachable.step current p h_current_reach hp_neighbor

/-- Helper: extract reachability from filtered neighbors -/
private theorem reachable_from_filtered_neighbor {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A)
    (start current p : Fin nP) (visited : List (Fin nP))
    (h_current_reach : Reachable S start current)
    (hp_new : p ∈ (navGraph S current).filter (fun q => !visited.contains q)) :
    Reachable S start p := by
  simp only [List.mem_filter] at hp_new
  exact neighbor_reachable S start current p h_current_reach hp_new.1

/-- BFS step preserves invariant -/
private theorem bfsStep_preserves_invariant {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start : Fin nP)
    (state : BFSState nP) (h_inv : BFSInvariant S start state) :
    BFSInvariant S start (bfsStep S state) := by
  unfold bfsStep
  split
  · exact h_inv  -- Empty queue: state unchanged
  · -- Non-empty queue: process current
    rename_i current rest h_queue
    have h_current_reach : Reachable S start current :=
      h_inv.2 current (by rw [h_queue]; simp only [List.mem_cons, true_or])
    constructor <;> intro p hp <;> simp only [List.mem_append] at hp
    · -- All in new visited are Reachable
      cases hp with
      | inl hp_old => exact h_inv.1 p hp_old
      | inr hp_new => exact reachable_from_filtered_neighbor S start current p _ h_current_reach hp_new
    · -- All in new queue are Reachable
      cases hp with
      | inl hp_rest => exact h_inv.2 p (by rw [h_queue]; simp only [List.mem_cons]; right; exact hp_rest)
      | inr hp_new => exact reachable_from_filtered_neighbor S start current p _ h_current_reach hp_new

/-- BFS.go preserves invariant and returns only Reachable nodes -/
private theorem bfs_go_soundness {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start : Fin nP)
    (state : BFSState nP) (remaining : Nat)
    (h_inv : BFSInvariant S start state) :
    ∀ p ∈ bfs.go S state remaining, Reachable S start p := by
  induction remaining generalizing state with
  | zero => unfold bfs.go; simp only [↓reduceIte]; exact h_inv.1
  | succ m ih =>
    unfold bfs.go; simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · exact h_inv.1  -- Queue empty
    · apply ih; exact bfsStep_preserves_invariant S start state h_inv  -- Recurse

/-- BFS soundness: If target is in BFS output, it's Reachable -/
private theorem bfs_soundness {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start target : Fin nP)
    (h : target ∈ bfs S start nP) :
    Reachable S start target := by
  unfold bfs at h
  have h_inv := bfs_initial_invariant S start
  exact bfs_go_soundness S start { visited := [start], queue := [start] } nP h_inv target h

/-- reachableFrom soundness: BFS only reports Reachable nodes -/
theorem reachableFrom_soundness {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start target : Fin nP)
    (h : target ∈ reachableFrom S start) :
    Reachable S start target := by
  unfold reachableFrom at h
  exact bfs_soundness S start target h

/-- If page is reachable, there exists a path to it -/
theorem reachable_has_path {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start target : Fin nP)
    (h : target ∈ reachableFrom S start) :
    ∃ path : List (Fin nP), path.head? = some start ∧ path.getLast? = some target :=
  reachable_has_path_ind S start target (reachableFrom_soundness S start target h)

/-- BFS path existence via inductive reachability (alias for backward compatibility) -/
theorem bfs_path_exists {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (start target : Fin nP)
    (_h_neq : start ≠ target) (h_reach : target ∈ reachableFrom S start) :
    ∃ path : List (Fin nP), path.head? = some start ∧ path.getLast? = some target :=
  reachable_has_path S start target h_reach

/-! ## Reporting -/

/-- Format reachability report -/
def formatReachabilityReport {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) (home : Fin nP) : String :=
  let reachable := reachableFrom S home
  let orphans := findOrphans S home
  let allReachable := allPagesReachable S home

  let header := "═══════════════════════════════════════════\n" ++
                "  Navigation Reachability Report\n" ++
                "═══════════════════════════════════════════\n\n"

  let stats := s!"Total Pages: {nP}\n" ++
               s!"Reachable from Home: {reachable.length}\n" ++
               s!"Orphaned Pages: {orphans.length}\n\n"

  let status := if allReachable then
                  "✅ Status: ALL PAGES REACHABLE\n"
                else
                  "❌ Status: ORPHANED PAGES DETECTED\n"

  let orphanList := if orphans.isEmpty then ""
                    else
                      "\nOrphaned Pages:\n" ++
                      String.intercalate "\n" (orphans.map fun p =>
                        let slug := S.slugOf p
                        s!"  • Page {p.val}: {slug.toString}")

  header ++ stats ++ status ++ orphanList

/-! ## Graph Statistics -/

/-- Compute average degree (links per page) -/
def avgDegree {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) : Float :=
  let totalLinks := (List.finRange nP).foldl (fun acc i => acc + (navGraph S i).length) 0
  if nP = 0 then 0.0
  else Float.ofNat totalLinks / Float.ofNat nP

/-- Find pages with no outgoing links (dead ends) -/
def findDeadEnds {nP nA : Nat} {A : Assets nA} (S : SiteV nP nA A) : List (Fin nP) :=
  (List.finRange nP).filter fun i =>
    (navGraph S i).isEmpty

end NoGoals
