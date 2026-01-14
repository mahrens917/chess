import Chess.Spec
import Chess.SemanticCaptureFlagLemmas

namespace Chess
namespace Rules

private theorem castleConfig_kingFrom_ne_kingTo (c : Color) (kingSide : Bool) :
    (castleConfig c kingSide).kingFrom ≠ (castleConfig c kingSide).kingTo := by
  cases c <;> cases kingSide <;> decide

theorem respectsGeometry_implies_fromSq_ne_toSq (gs : GameState) (m : Move) :
    respectsGeometry gs m →
    m.fromSq ≠ m.toSq := by
  intro hGeom
  unfold respectsGeometry at hGeom
  cases hpt : m.piece.pieceType <;> simp [hpt] at hGeom
  · -- King
    by_cases hCastle : m.isCastle
    ·
      have hCastleGeom :
          ∃ cfg : CastleConfig,
            cfg.kingFrom = m.fromSq ∧
              cfg.kingTo = m.toSq ∧
                (cfg = castleConfig m.piece.color true ∨ cfg = castleConfig m.piece.color false) := by
        simpa [hCastle] using hGeom
      rcases hCastleGeom with ⟨cfg, hFrom, hTo, hCfg⟩
      intro hEq
      have hKingEq : cfg.kingFrom = cfg.kingTo := by
        calc
          cfg.kingFrom = m.fromSq := hFrom
          _ = m.toSq := hEq
          _ = cfg.kingTo := hTo.symm
      cases hCfg with
      | inl hEqCfg =>
          subst hEqCfg
          exact (castleConfig_kingFrom_ne_kingTo m.piece.color true) hKingEq
      | inr hEqCfg =>
          subst hEqCfg
          exact (castleConfig_kingFrom_ne_kingTo m.piece.color false) hKingEq
    · -- Normal king step
      have hStep : Movement.isKingStep m.fromSq m.toSq := by
        simpa [hCastle] using hGeom
      exact hStep.1
  · -- Queen
    exact (hGeom.1.elim (fun h => h.1) (fun h => h.1))
  · -- Rook
    exact hGeom.1.1
  · -- Bishop
    exact hGeom.1.1
  · -- Knight
    exact hGeom.1
  · -- Pawn
    by_cases hCap : m.isCapture
    · -- capture (incl EP)
      cases hEP : m.isEnPassant <;> simp [hCap, hEP] at hGeom
      · exact hGeom.1.1
      · exact hGeom.1.1
    · -- quiet pawn
      have hQuiet :
          Movement.isPawnAdvance m.piece.color m.fromSq m.toSq ∧
            pathClear gs.board m.fromSq m.toSq = true ∧
              (Movement.rankDiff m.fromSq m.toSq = -2 * Movement.pawnDirection m.piece.color →
                m.fromSq.rankNat = pawnStartRank m.piece.color) := by
        simpa [hCap] using hGeom
      have hAdv : Movement.isPawnAdvance m.piece.color m.fromSq m.toSq := hQuiet.1
      exact hAdv.1

theorem fideLegalSemantic_implies_basicLegalAndSafe (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    basicLegalAndSafe gs m = true := by
  intro hSem
  rcases hSem with
    ⟨hTurn, hFrom, hGeom, hDest, hCapSpec, hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, _hRookFields⟩

  have hOrigin : originHasPiece gs m = true := by
    simp [originHasPiece, hFrom]
  have hTurnB : turnMatches gs m = true := by
    simp [turnMatches, hTurn]
  have hDestB : destinationFriendlyFree gs m = true :=
    hDest
  have hCapB : captureFlagConsistent gs m = true := by
    exact captureFlagConsistent_of_destinationFriendlyFree_and_captureFlagConsistentWithEP
      gs m hDest hCapSpec
  have hDiff : m.fromSq ≠ m.toSq :=
    respectsGeometry_implies_fromSq_ne_toSq gs m hGeom
  have hDiffB : squaresDiffer m = true := by
    simp [squaresDiffer, hDiff]

  have hBasic : basicMoveLegalBool gs m = true := by
    simp [basicMoveLegalBool, hOrigin, hTurnB, hDestB, hCapB, hDiffB]

  have hNotCheck' : ¬(inCheck (gs.movePiece m).board gs.toMove) := by
    simpa using hNotCheck
  have hInCheckFalse : inCheck (gs.movePiece m).board gs.toMove = false := by
    cases hChk : inCheck (gs.movePiece m).board gs.toMove <;> simp [hChk] at hNotCheck'
    rfl

  unfold basicLegalAndSafe
  simp [hBasic, hInCheckFalse]

end Rules
end Chess
