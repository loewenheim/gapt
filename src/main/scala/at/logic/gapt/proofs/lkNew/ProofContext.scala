package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr.LambdaExpression
import at.logic.gapt.expr.hol.HOLSignature
import at.logic.gapt.expr.hol.HOLSignature.HOLSignature
import at.logic.gapt.expr.hol.HOLSignature.HOLSignature
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkNew.ProofContext.DefinitionMap

/**
 * Created by sebastian on 11/10/15.
 */
case class ProofContext( signature: HOLSignature, defmap: DefinitionMap, theory: Set[HOLSequent] ) {
  for ( sequent <- theory )
    require( HOLSignature( sequent ) subsetOf signature, s"Sequent $sequent is not in signature $signature." )

  /**
   * Unifies two contexts.
   *
   * This is only possible if the definition maps of this and that agree on the intersection of their domains.
   * @param that Another proof context.
   * @return A proof context containing the signatures, definitions and theory axioms of both this and that.
   */
  def ++( that: ProofContext ): ProofContext = ProofContext(
    this.signature ++ that.signature,
    mergeMaps( defmap, that.defmap ),
    this.theory ++ that.theory
  )

  /**
   * Adds a definition to a context.
   *
   * FIXME: This needs to be reworked.
   *
   * @param t The expression to be defined.
   * @param u The definition for t.
   * @return A context that contains t → u in its definition map, if consistent.
   */
  def addDefinition( t: LambdaExpression, u: LambdaExpression ): ProofContext = {
    defmap.get( t ) match {
      case Some( `u` ) => this
      case Some( v )   => throw new IllegalArgumentException( s"Cannot add definition $t := $u to map: $t is already defined as $v." )
      case None        => this.copy( defmap = this.defmap + ( t -> u ) )
    }
  }

  /**
   * Merges two maps if they agree on the intersection of their domains.
   */
  private def mergeMaps[A, B]( mapOne: Map[A, B], mapTwo: Map[A, B] ): Map[A, B] = {
    mapOne.foldLeft( mapTwo ) { ( acc, p ) =>
      acc.get( p._1 ) match {
        case Some( v ) if v != p._2 => //There is a collision between the maps
          throw new IllegalArgumentException( s"Cannot merge maps: They disagree on element ${p._1}." )
        case Some( v ) => acc
        case None      => acc + p
      }
    }
  }
}

object ProofContext {
  type DefinitionMap = Map[LambdaExpression, LambdaExpression]

  /**
   *
   * @return The empty proof context.
   */
  def apply(): ProofContext = ProofContext( HOLSignature(), Map(), Set() )

}