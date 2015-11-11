package at.logic.gapt.expr.hol

import java.lang.IllegalArgumentException

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent

/**
 * Created by sebastian on 11/10/15.
 */
object HOLSignature {
  type HOLSignature = Set[Const]

  def apply(): HOLSignature = Set.empty[Const]
  def apply( expr: LambdaExpression ): HOLSignature = expr match {
    case Var( _, _ ) => Set()
    case c @ Const( name, _ ) =>
      name match {
        case "∀" | "∃" | "¬" | "∨" | "∧" | "⊃" | "⊥" | "⊤" => Set()
        case _ => Set( c )
      }
    case App( fun, arg ) =>
      val newSignature = HOLSignature( fun ) ++ HOLSignature( arg )

      for ( ( name, symbols ) <- newSignature.groupBy( _.name ) ) if ( name != "=" )
        require( symbols.size == 1, s"Incompatible signatures of $fun and $arg: Constant symbol $name is not unique." )

      newSignature

    case Abs( x, arg ) => HOLSignature( arg )
  }

  def apply( sequent: Sequent[LambdaExpression] ): HOLSignature =
    if ( sequent.isEmpty )
      HOLSignature()
    else
      sequent.elements map apply reduceLeft ( _ ++ _ )
}