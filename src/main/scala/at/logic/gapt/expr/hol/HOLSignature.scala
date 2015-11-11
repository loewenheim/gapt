package at.logic.gapt.expr.hol

import java.lang.IllegalArgumentException

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent

/**
 * Created by sebastian on 11/10/15.
 */
object HOLSignature {
  /**
   * Type alias for Set[Const].
   */
  type HOLSignature = Set[Const]

  /**
   *
   * @return The empty HOLSignature.
   */
  def apply(): HOLSignature = Set.empty[Const]

  /**
   * Computes the signature of an expression.
   *
   * @param expr A LambdaExpression.
   * @return The set of constants occurring in expr.
   */
  def apply( expr: LambdaExpression ): HOLSignature = expr match {
    case Var( _, _ )        => Set()
    case _: LogicalConstant => Set()
    case c: Const           => Set( c )
    case App( fun, arg )    => HOLSignature( fun ) ++ HOLSignature( arg )
    case Abs( x, arg )      => HOLSignature( arg )
  }

  /**
   * Computes the signature of a sequent.
   *
   * @param sequent A Sequent of LambdaExpressions.
   * @return The set of constants occurring in sequent.
   */
  def apply( sequent: Sequent[LambdaExpression] ): HOLSignature =
    if ( sequent.isEmpty )
      HOLSignature()
    else
      sequent.elements map apply reduceLeft ( _ ++ _ )
}