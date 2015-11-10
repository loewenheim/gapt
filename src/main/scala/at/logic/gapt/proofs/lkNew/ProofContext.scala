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

  def ++( that: ProofContext ): ProofContext = {
    val newSignature = signature ++ that.signature

    for ( ( name, symbols ) <- newSignature.groupBy( _.name ) ) if ( name != "=" )
      require( symbols.size == 1, s"Incompatible signatures of $this and $that: Constant symbol $name is not unique." )

    val newDefMap = mergeMaps( defmap, that.defmap )

    ProofContext( newSignature, newDefMap, this.theory ++ that.theory )
  }

  def addDefinition( t: LambdaExpression, u: LambdaExpression ): ProofContext = {
    defmap.get( t ) match {
      case Some( `u` ) => this
      case Some( v )   => throw new IllegalArgumentException( s"Cannot add definition $t := $u to map: $t is already defined as $v." )
      case None        => this.copy( defmap = this.defmap + ( t -> u ) )
    }
  }

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

  def apply(): ProofContext = ProofContext( HOLSignature(), Map(), Set() )

}