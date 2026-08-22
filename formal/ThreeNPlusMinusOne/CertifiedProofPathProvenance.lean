import ThreeNPlusMinusOne.ProofPathProvenance
import ThreeNPlusMinusOne.CertifiedOccurrenceRefinement

set_option autoImplicit false

/-!
# First-exit provenance for data-level proof certificates

Unlike proposition-valued finite proof trees, a data-level certificate retains
the exact selected branch at every WIN node.  This file gives the first-exit
alternative directly on that carrier: a legal path is covered by the retained
certificate, or it exposes a strictly lower already stored LOSS certificate.
The latter is immediately a legal data-level forest replacement.
-/

namespace ThreeNPlusMinusOne

mutual
  /-- A path follows the retained selected branch of a data-level WIN
certificate and either stored branch of a data-level LOSS certificate. -/
  inductive WinningCertificateCovers :
      {position height : Nat} → WinningCertificate position height → List Nat → Prop
    | stop {position height : Nat} (certificate : WinningCertificate position height) :
        WinningCertificateCovers certificate [position]
    | moveA {position height : Nat} (nonterminal : 0 < position)
        (reply : LosingCertificate (A position) height) {path : List Nat}
        (covered : LosingCertificateCovers reply path) :
        WinningCertificateCovers (WinningCertificate.moveA nonterminal reply)
          (position :: path)
    | moveB {position height : Nat} (nonterminal : 0 < position)
        (reply : LosingCertificate (B position) height) {path : List Nat}
        (covered : LosingCertificateCovers reply path) :
        WinningCertificateCovers (WinningCertificate.moveB nonterminal reply)
          (position :: path)

  inductive LosingCertificateCovers :
      {position height : Nat} → LosingCertificate position height → List Nat → Prop
    | stop {position height : Nat} (certificate : LosingCertificate position height) :
        LosingCertificateCovers certificate [position]
    | repliesA {position heightA heightB : Nat} (nonterminal : 0 < position)
        (replyA : WinningCertificate (A position) heightA)
        (replyB : WinningCertificate (B position) heightB) {path : List Nat}
        (covered : WinningCertificateCovers replyA path) :
        LosingCertificateCovers
          (LosingCertificate.replies nonterminal replyA replyB) (position :: path)
    | repliesB {position heightA heightB : Nat} (nonterminal : 0 < position)
        (replyA : WinningCertificate (A position) heightA)
        (replyB : WinningCertificate (B position) heightB) {path : List Nat}
        (covered : WinningCertificateCovers replyB path) :
        LosingCertificateCovers
          (LosingCertificate.replies nonterminal replyA replyB) (position :: path)
end

/- A child token extracted from the concrete stored certificate of its parent. -/
inductive CertifiedTokenChild : CertifiedProofToken → CertifiedProofToken → Prop
  | winningA {position height : Nat} (nonterminal : 0 < position)
      (reply : LosingCertificate (A position) height) :
      CertifiedTokenChild
        (.winning ⟨position, height + 1,
          WinningCertificate.moveA nonterminal reply⟩)
        (.losing ⟨A position, height, reply⟩)
  | winningB {position height : Nat} (nonterminal : 0 < position)
      (reply : LosingCertificate (B position) height) :
      CertifiedTokenChild
        (.winning ⟨position, height + 1,
          WinningCertificate.moveB nonterminal reply⟩)
        (.losing ⟨B position, height, reply⟩)
  | losingA {position heightA heightB : Nat} (nonterminal : 0 < position)
      (replyA : WinningCertificate (A position) heightA)
      (replyB : WinningCertificate (B position) heightB) :
      CertifiedTokenChild
        (.losing ⟨position, max heightA heightB + 1,
          LosingCertificate.replies nonterminal replyA replyB⟩)
        (.winning ⟨A position, heightA, replyA⟩)
  | losingB {position heightA heightB : Nat} (nonterminal : 0 < position)
      (replyA : WinningCertificate (A position) heightA)
      (replyB : WinningCertificate (B position) heightB) :
      CertifiedTokenChild
        (.losing ⟨position, max heightA heightB + 1,
          LosingCertificate.replies nonterminal replyA replyB⟩)
        (.winning ⟨B position, heightB, replyB⟩)

theorem CertifiedTokenChild.move
    {parent child : CertifiedProofToken}
    (edge : CertifiedTokenChild parent child) :
    ConjugatedMove child.position parent.position := by
  cases edge with
  | winningA nonterminal reply =>
      exact ⟨nonterminal, Or.inl rfl⟩
  | winningB nonterminal reply =>
      exact ⟨nonterminal, Or.inr rfl⟩
  | losingA nonterminal replyA replyB =>
      exact ⟨nonterminal, Or.inl rfl⟩
  | losingB nonterminal replyA replyB =>
      exact ⟨nonterminal, Or.inr rfl⟩

theorem CertifiedTokenChild.height_lower
    {parent child : CertifiedProofToken}
    (edge : CertifiedTokenChild parent child) :
    child.height < parent.height := by
  cases edge <;> simp [CertifiedProofToken.height] <;> omega

/-- A finite traversal whose tokens are exact nested children of the preceding
stored certificate. -/
inductive StoredCertificateRoute : List CertifiedProofToken → List Nat → Prop
  | singleton (token : CertifiedProofToken) :
      StoredCertificateRoute [token] [token.position]
  | extend {parent child : CertifiedProofToken}
      {tail : List CertifiedProofToken} {path : List Nat}
      (edge : CertifiedTokenChild parent child)
      (route : StoredCertificateRoute (child :: tail) path) :
      StoredCertificateRoute (parent :: child :: tail) (parent.position :: path)

/-- The strict-height invariant carried by every adjacent edge of a stored
certificate route. -/
inductive StrictCertifiedTokenChain : List CertifiedProofToken → Prop
  | singleton (token : CertifiedProofToken) :
      StrictCertifiedTokenChain [token]
  | extend {parent child : CertifiedProofToken}
      {tail : List CertifiedProofToken}
      (lower : child.height < parent.height)
      (chain : StrictCertifiedTokenChain (child :: tail)) :
      StrictCertifiedTokenChain (parent :: child :: tail)

theorem StoredCertificateRoute.starts_at
    {token : CertifiedProofToken} {tail : List CertifiedProofToken}
    {path : List Nat}
    (route : StoredCertificateRoute (token :: tail) path) :
    ∃ rest, path = token.position :: rest := by
  cases route with
  | singleton token =>
      exact ⟨[], rfl⟩
  | extend edge route =>
      exact ⟨_, rfl⟩

theorem StoredCertificateRoute.strictChain
    {tokens : List CertifiedProofToken} {path : List Nat}
    (route : StoredCertificateRoute tokens path) :
    StrictCertifiedTokenChain tokens := by
  induction route with
  | singleton token =>
      exact StrictCertifiedTokenChain.singleton token
  | extend edge route ih =>
      exact StrictCertifiedTokenChain.extend edge.height_lower ih

theorem StoredCertificateRoute.gamePath
    {tokens : List CertifiedProofToken} {path : List Nat}
    (route : StoredCertificateRoute tokens path) :
    GamePath path := by
  induction route with
  | singleton token =>
      trivial
  | extend edge route ih =>
      obtain ⟨rest, pathEq⟩ := StoredCertificateRoute.starts_at route
      cases pathEq
      exact ⟨edge.move, ih⟩

/- A covered path has a concrete route of retained nested certificate tokens. -/
mutual
  theorem WinningCertificateCovers.toStoredRoute :
      {position height : Nat} → {certificate : WinningCertificate position height} →
        {path : List Nat} → WinningCertificateCovers certificate path →
          ∃ tail,
            StoredCertificateRoute
              (CertifiedProofToken.winning ⟨position, height, certificate⟩ :: tail)
              path
    | _, _, _, _, .stop certificate =>
        ⟨[], StoredCertificateRoute.singleton
          (CertifiedProofToken.winning ⟨_, _, certificate⟩)⟩
    | _, _, _, _, .moveA nonterminal reply covered => by
        obtain ⟨tail, route⟩ := LosingCertificateCovers.toStoredRoute covered
        exact ⟨CertifiedProofToken.losing ⟨_, _, reply⟩ :: tail,
          StoredCertificateRoute.extend
          (CertifiedTokenChild.winningA nonterminal reply) route⟩
    | _, _, _, _, .moveB nonterminal reply covered => by
        obtain ⟨tail, route⟩ := LosingCertificateCovers.toStoredRoute covered
        exact ⟨CertifiedProofToken.losing ⟨_, _, reply⟩ :: tail,
          StoredCertificateRoute.extend
          (CertifiedTokenChild.winningB nonterminal reply) route⟩

  theorem LosingCertificateCovers.toStoredRoute :
      {position height : Nat} → {certificate : LosingCertificate position height} →
        {path : List Nat} → LosingCertificateCovers certificate path →
          ∃ tail,
            StoredCertificateRoute
              (CertifiedProofToken.losing ⟨position, height, certificate⟩ :: tail)
              path
    | _, _, _, _, .stop certificate =>
        ⟨[], StoredCertificateRoute.singleton
          (CertifiedProofToken.losing ⟨_, _, certificate⟩)⟩
    | _, _, _, _, .repliesA nonterminal replyA replyB covered => by
        obtain ⟨tail, route⟩ := WinningCertificateCovers.toStoredRoute covered
        exact ⟨CertifiedProofToken.winning ⟨_, _, replyA⟩ :: tail,
          StoredCertificateRoute.extend
          (CertifiedTokenChild.losingA nonterminal replyA replyB) route⟩
    | _, _, _, _, .repliesB nonterminal replyA replyB covered => by
        obtain ⟨tail, route⟩ := WinningCertificateCovers.toStoredRoute covered
        exact ⟨CertifiedProofToken.winning ⟨_, _, replyB⟩ :: tail,
          StoredCertificateRoute.extend
          (CertifiedTokenChild.losingB nonterminal replyA replyB) route⟩
end

theorem CertifiedWinningToken.covered_stored_route
    (token : CertifiedWinningToken) {rest : List Nat}
    (covered : WinningCertificateCovers token.certificate
      (token.position :: rest)) :
    ∃ tail,
      StoredCertificateRoute
        (CertifiedProofToken.winning token :: tail) (token.position :: rest) := by
  cases token with
  | mk position height certificate =>
      exact WinningCertificateCovers.toStoredRoute covered

theorem WinningCertificateCovers.starts_at :
    {position height : Nat} → {certificate : WinningCertificate position height} →
      {path : List Nat} → WinningCertificateCovers certificate path →
        ∃ rest, path = position :: rest
  | _, _, _, _, .stop _ => ⟨[], rfl⟩
  | _, _, _, _, .moveA _ _ _ => ⟨_, rfl⟩
  | _, _, _, _, .moveB _ _ _ => ⟨_, rfl⟩

theorem LosingCertificateCovers.starts_at :
    {position height : Nat} → {certificate : LosingCertificate position height} →
      {path : List Nat} → LosingCertificateCovers certificate path →
        ∃ rest, path = position :: rest
  | _, _, _, _, .stop _ => ⟨[], rfl⟩
  | _, _, _, _, .repliesA _ _ _ _ => ⟨_, rfl⟩
  | _, _, _, _, .repliesB _ _ _ _ => ⟨_, rfl⟩

/- Every data-level coverage witness follows actual legal conjugated moves. -/
mutual
  theorem WinningCertificateCovers.gamePath :
      {position height : Nat} → {certificate : WinningCertificate position height} →
        {path : List Nat} → WinningCertificateCovers certificate path →
          GamePath path
    | _, _, _, _, .stop _ => trivial
    | _, _, _, _, .moveA nonterminal reply covered => by
        obtain ⟨rest, tailEq⟩ := LosingCertificateCovers.starts_at covered
        cases tailEq
        exact ⟨⟨nonterminal, Or.inl rfl⟩,
          LosingCertificateCovers.gamePath covered⟩
    | _, _, _, _, .moveB nonterminal reply covered => by
        obtain ⟨rest, tailEq⟩ := LosingCertificateCovers.starts_at covered
        cases tailEq
        exact ⟨⟨nonterminal, Or.inr rfl⟩,
          LosingCertificateCovers.gamePath covered⟩

  theorem LosingCertificateCovers.gamePath :
      {position height : Nat} → {certificate : LosingCertificate position height} →
        {path : List Nat} → LosingCertificateCovers certificate path →
          GamePath path
    | _, _, _, _, .stop _ => trivial
    | _, _, _, _, .repliesA nonterminal replyA replyB covered => by
        obtain ⟨rest, tailEq⟩ := WinningCertificateCovers.starts_at covered
        cases tailEq
        exact ⟨⟨nonterminal, Or.inl rfl⟩,
          WinningCertificateCovers.gamePath covered⟩
    | _, _, _, _, .repliesB nonterminal replyA replyB covered => by
        obtain ⟨rest, tailEq⟩ := WinningCertificateCovers.starts_at covered
        cases tailEq
        exact ⟨⟨nonterminal, Or.inr rfl⟩,
          WinningCertificateCovers.gamePath covered⟩
end

/- Forgetting branch-choice data takes data-level coverage to the earlier
proposition-level coverage relation on the erased finite tree. -/
mutual
  theorem WinningCertificateCovers.toWinningTreeCovers :
      {position height : Nat} → {certificate : WinningCertificate position height} →
        {path : List Nat} → WinningCertificateCovers certificate path →
          WinningTreeCovers (WinningCertificate.toWinningTree certificate) path
    | _, _, _, _, .stop certificate =>
        WinningTreeCovers.stop (WinningCertificate.toWinningTree certificate)
    | _, _, _, _, .moveA nonterminal reply covered =>
        WinningTreeCovers.moveA nonterminal
          (LosingCertificate.toLosingTree reply)
          (LosingCertificateCovers.toLosingTreeCovers covered)
    | _, _, _, _, .moveB nonterminal reply covered =>
        WinningTreeCovers.moveB nonterminal
          (LosingCertificate.toLosingTree reply)
          (LosingCertificateCovers.toLosingTreeCovers covered)

  theorem LosingCertificateCovers.toLosingTreeCovers :
      {position height : Nat} → {certificate : LosingCertificate position height} →
        {path : List Nat} → LosingCertificateCovers certificate path →
          LosingTreeCovers (LosingCertificate.toLosingTree certificate) path
    | _, _, _, _, .stop certificate =>
        LosingTreeCovers.stop (LosingCertificate.toLosingTree certificate)
    | _, _, _, _, .repliesA nonterminal replyA replyB covered =>
        LosingTreeCovers.repliesA nonterminal
          (WinningCertificate.toWinningTree replyA)
          (WinningCertificate.toWinningTree replyB)
          (WinningCertificateCovers.toWinningTreeCovers covered)
    | _, _, _, _, .repliesB nonterminal replyA replyB covered =>
        LosingTreeCovers.repliesB nonterminal
          (WinningCertificate.toWinningTree replyA)
          (WinningCertificate.toWinningTree replyB)
          (WinningCertificateCovers.toWinningTreeCovers covered)
end

private theorem certificate_covers_or_lower_loss_by_height :
    ∀ height : Nat,
      (∀ {position : Nat} (certificate : WinningCertificate position height)
          {rest : List Nat}, GamePath (position :: rest) →
          WinningCertificateCovers certificate (position :: rest) ∨
            ∃ loss : CertifiedLosingToken, loss.height < height) ∧
      (∀ {position : Nat} (certificate : LosingCertificate position height)
          {rest : List Nat}, GamePath (position :: rest) →
          LosingCertificateCovers certificate (position :: rest) ∨
            ∃ loss : CertifiedLosingToken, loss.height < height) := by
  intro height
  induction height using Nat.strongRecOn with
  | ind height ih =>
      constructor
      · intro position certificate rest path
        let token : CertifiedWinningToken := ⟨position, height, certificate⟩
        cases rest with
        | nil =>
            exact Or.inl (WinningCertificateCovers.stop certificate)
        | cons next rest =>
            change ConjugatedMove next position ∧ GamePath (next :: rest) at path
            rcases path with ⟨move, tailPath⟩
            unfold ConjugatedMove at move
            cases certificate with
            | @moveA _ childHeight nonterminal reply =>
                rcases move.2 with nextA | nextB
                · subst next
                  obtain covered | lower :=
                    (ih childHeight (by omega)).2 reply tailPath
                  · exact Or.inl
                      (WinningCertificateCovers.moveA nonterminal reply covered)
                  · rcases lower with ⟨loss, lossLower⟩
                    exact Or.inr ⟨loss, by omega⟩
                · subst next
                  obtain ⟨loss, _, lossLower⟩ := token.selected_loss_strict
                  exact Or.inr ⟨loss, by simpa [token] using lossLower⟩
            | @moveB _ childHeight nonterminal reply =>
                rcases move.2 with nextA | nextB
                · subst next
                  obtain ⟨loss, _, lossLower⟩ := token.selected_loss_strict
                  exact Or.inr ⟨loss, by simpa [token] using lossLower⟩
                · subst next
                  obtain covered | lower :=
                    (ih childHeight (by omega)).2 reply tailPath
                  · exact Or.inl
                      (WinningCertificateCovers.moveB nonterminal reply covered)
                  · rcases lower with ⟨loss, lossLower⟩
                    exact Or.inr ⟨loss, by omega⟩
      · intro position certificate rest path
        cases rest with
        | nil =>
            exact Or.inl (LosingCertificateCovers.stop certificate)
        | cons next rest =>
            change ConjugatedMove next position ∧ GamePath (next :: rest) at path
            rcases path with ⟨move, tailPath⟩
            unfold ConjugatedMove at move
            cases certificate with
            | terminal =>
                omega
            | @replies _ heightA heightB nonterminal replyA replyB =>
                rcases move.2 with nextA | nextB
                · subst next
                  obtain covered | lower :=
                    (ih heightA (by omega)).1 replyA tailPath
                  · exact Or.inl
                      (LosingCertificateCovers.repliesA nonterminal replyA replyB
                        covered)
                  · rcases lower with ⟨loss, lossLower⟩
                    exact Or.inr ⟨loss, by omega⟩
                · subst next
                  obtain covered | lower :=
                    (ih heightB (by omega)).1 replyB tailPath
                  · exact Or.inl
                      (LosingCertificateCovers.repliesB nonterminal replyA replyB
                        covered)
                  · rcases lower with ⟨loss, lossLower⟩
                    exact Or.inr ⟨loss, by omega⟩

/-- First-exit provenance for a data-level WIN certificate. A legal path
either remains covered by its stored selection or exposes a strictly lower
stored LOSS certificate. -/
theorem WinningCertificate.covers_or_lower_loss
    {position height : Nat} (certificate : WinningCertificate position height)
    {rest : List Nat} (path : GamePath (position :: rest)) :
    WinningCertificateCovers certificate (position :: rest) ∨
      ∃ loss : CertifiedLosingToken, loss.height < height := by
  exact (certificate_covers_or_lower_loss_by_height height).1 certificate path

/-- Companion first-exit provenance for a data-level LOSS certificate. -/
theorem LosingCertificate.covers_or_lower_loss
    {position height : Nat} (certificate : LosingCertificate position height)
    {rest : List Nat} (path : GamePath (position :: rest)) :
    LosingCertificateCovers certificate (position :: rest) ∨
      ∃ loss : CertifiedLosingToken, loss.height < height := by
  exact (certificate_covers_or_lower_loss_by_height height).2 certificate path

theorem CertifiedWinningToken.covers_path_or_lower_loss
    (token : CertifiedWinningToken) {rest : List Nat}
    (path : GamePath (token.position :: rest)) :
    WinningCertificateCovers token.certificate (token.position :: rest) ∨
      ∃ loss : CertifiedLosingToken, loss.height < token.height := by
  exact token.certificate.covers_or_lower_loss path

/-- A certificate-level first exit immediately becomes an exact lower
replacement in the data-level occurrence macro forest. -/
theorem CertifiedWinningToken.covers_path_or_lower_loss_outer_step
    (token : CertifiedWinningToken) {rest : List Nat}
    (path : GamePath (token.position :: rest))
    {before after innerForest : CertifiedProofForest}
    (base : MacroConfiguration) :
    WinningCertificateCovers token.certificate (token.position :: rest) ∨
      ∃ loss : CertifiedLosingToken,
        loss.height < token.height ∧
          CertifiedOccurrenceMacroStep
            { base := base
              outerForest :=
                before ++ [CertifiedProofToken.losing loss] ++ after
              innerForest := innerForest }
            { base := base
              outerForest :=
                before ++ [CertifiedProofToken.winning token] ++ after
              innerForest := innerForest } := by
  obtain covered | ⟨loss, lower⟩ := token.covers_path_or_lower_loss path
  · exact Or.inl covered
  · refine Or.inr ⟨loss, lower, ?_⟩
    refine CertifiedOccurrenceMacroStep.outerForest
      (next :=
        { base := base
          outerForest := before ++ [CertifiedProofToken.losing loss] ++ after
          innerForest := innerForest })
      (current :=
        { base := base
          outerForest := before ++ [CertifiedProofToken.winning token] ++ after
          innerForest := innerForest })
      rfl rfl ?_
    simpa [List.append_assoc] using
      (certifiedProofTokenReplacement_single
        (before := before) (after := after)
        (parent := CertifiedProofToken.winning token)
        (child := CertifiedProofToken.losing loss)
        (by simpa [CertifiedProofToken.height] using lower))

end ThreeNPlusMinusOne
