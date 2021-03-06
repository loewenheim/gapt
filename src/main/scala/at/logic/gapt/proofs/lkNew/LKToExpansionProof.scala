package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr.Eq
import at.logic.gapt.proofs.{ Sequent, Suc, Ant, SequentIndex }
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.utils.logging.Logger

/**
 * Created by sebastian on 9/10/15.
 */
object LKToExpansionProof extends Logger {

  /**
   * Extracts an expansion sequent Ex(π) from an LKProof π.
   * Dp(Ex(π)) might not be tautological, e.g. if π contains quantified cuts.
   * The induction rule is not supported!
   *
   * @param proof The proof π.
   * @return The expansion proof Ex(π).
   */
  def apply( proof: LKProof ): ExpansionSequent = proof match {

    // Axioms
    case LogicalAxiom( atom )                    => Sequent( Seq( ETAtom( atom ) ), Seq( ETAtom( atom ) ) )

    case ReflexivityAxiom( s )                   => Sequent( Seq(), Seq( ETAtom( Eq( s, s ) ) ) )

    case TopAxiom                                => Sequent( Seq(), Seq( ETTop ) )

    case BottomAxiom                             => Sequent( Seq( ETBottom ), Seq() )

    case TheoryAxiom( sequent )                  => sequent map { i => ETAtom( i ) }

    // Structural rules
    case WeakeningLeftRule( subProof, formula )  => ETWeakening( formula ) +: apply( subProof )

    case WeakeningRightRule( subProof, formula ) => apply( subProof ) :+ ETWeakening( formula )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val subSequent = apply( subProof )
      merge( ETMerge( subSequent( aux1 ), subSequent( aux2 ) ) ) +: subSequent.delete( aux1, aux2 )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val subSequent = apply( subProof )
      subSequent.delete( aux1, aux2 ) :+ merge( ETMerge( subSequent( aux1 ), subSequent( aux2 ) ) )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val leftSubSequent = apply( leftSubProof ).delete( aux1 )
      val rightSubSequent = apply( rightSubProof ).delete( aux2 )
      leftSubSequent ++ rightSubSequent

    // Propositional rules
    case NegLeftRule( subProof, aux ) =>
      val ( subTree, subSequent ) = apply( subProof ).focus( aux )
      ETNeg( subTree ) +: subSequent

    case NegRightRule( subProof, aux ) =>
      val ( subTree, subSequent ) = apply( subProof ).focus( aux )
      subSequent :+ ETNeg( subTree )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val subSequent = apply( subProof )
      ETAnd( subSequent( aux1 ), subSequent( aux2 ) ) +: subSequent.delete( aux1, aux2 )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubTree, leftSubSequent ) = apply( leftSubProof ).focus( aux1 )
      val ( rightSubTree, rightSubSequent ) = apply( rightSubProof ).focus( aux2 )
      ( leftSubSequent ++ rightSubSequent ) :+ ETAnd( leftSubTree, rightSubTree )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubTree, leftSubSequent ) = apply( leftSubProof ).focus( aux1 )
      val ( rightSubTree, rightSubSequent ) = apply( rightSubProof ).focus( aux2 )
      ETOr( leftSubTree, rightSubTree ) +: ( leftSubSequent ++ rightSubSequent )

    case OrRightRule( subProof, aux1, aux2 ) =>
      val subSequent = apply( subProof )
      subSequent.delete( aux1, aux2 ) :+ ETOr( subSequent( aux1 ), subSequent( aux2 ) )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubTree, leftSubSequent ) = apply( leftSubProof ).focus( aux1 )
      val ( rightSubTree, rightSubSequent ) = apply( rightSubProof ).focus( aux2 )
      ETImp( leftSubTree, rightSubTree ) +: ( leftSubSequent ++ rightSubSequent )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val subSequent = apply( subProof )
      subSequent.delete( aux1, aux2 ) :+ ETImp( subSequent( aux1 ), subSequent( aux2 ) )

    // Quantifier rules
    case ForallLeftRule( subProof, aux, _, t, _ ) =>
      val ( subTree, subSequent ) = apply( subProof ).focus( aux )
      merge( ETWeakQuantifier( proof.mainFormulas.head, Seq( subTree -> t ) ) ) +: subSequent

    case ForallRightRule( subProof, aux, eigen, _ ) =>
      val ( subTree, subSequent ) = apply( subProof ).focus( aux )
      subSequent :+ ETStrongQuantifier( proof.mainFormulas.head, eigen, subTree )

    case ExistsLeftRule( subProof, aux, eigen, _ ) =>
      val ( subTree, subSequent ) = apply( subProof ).focus( aux )
      ETStrongQuantifier( proof.mainFormulas.head, eigen, subTree ) +: subSequent

    case ExistsRightRule( subProof, aux, _, t, _ ) =>
      val ( subTree, subSequent ) = apply( subProof ).focus( aux )
      subSequent :+ merge( ETWeakQuantifier( proof.mainFormulas.head, Seq( subTree -> t ) ) )

    // Equality rules
    case EqualityLeftRule( subProof, eq, aux, pos ) =>
      val ( subTree, subSequent ) = apply( subProof ).focus( aux )
      val repTerm = proof.mainFormulas.head( pos )
      val newTree = merge( replaceAtHOLPosition( subTree, pos, repTerm ) )
      newTree +: subSequent

    case EqualityRightRule( subProof, eq, aux, pos ) =>
      val ( subTree, subSequent ) = apply( subProof ).focus( aux )
      val repTerm = proof.mainFormulas.head( pos )
      val newTree = merge( replaceAtHOLPosition( subTree, pos, repTerm ) )
      subSequent :+ newTree

    case _ => throw new IllegalArgumentException( s"Unsupported inference rule: ${proof.longName}." )
  }
}
