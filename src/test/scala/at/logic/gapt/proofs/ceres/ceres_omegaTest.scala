package at.logic.gapt.proofs.ceres

import at.logic.gapt.algorithms.rewriting.DefinitionElimination
import at.logic.gapt.expr._
import at.logic.gapt.formats.llk.HybridLatexParser
import at.logic.gapt.proofs.ceres.projections.Projections
import at.logic.gapt.proofs.ceres.struct.StructCreators
import at.logic.gapt.proofs.{ Ant, Suc, HOLSequent }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.utils.testing.ClasspathFileCopier
import org.specs2.mutable._

import at.logic.gapt.proofs.lksk._
import at.logic.gapt.proofs.ral._
import at.logic.gapt.proofs.ceres.clauseSets._

/**
 * Created by marty on 6/18/15.
 */
class ceres_omegaTest extends Specification with ClasspathFileCopier {

  def prepareProof( file: String, proofname: String ) = {
    val p = HybridLatexParser( tempCopyOfClasspathFile( file ) )
    val elp = AtomicExpansion( DefinitionElimination( p.Definitions, regularize( p.proof( proofname ) ) ) )
    val selp = LKToLKsk( elp )
    val struct = StructCreators.extract( selp )
    val ls = SimpleStandardClauseSet( struct )
    val proj = Projections( selp )
    ( selp, ls, struct, proj )
  }

  def refutation1( cs: Set[HOLSequent] ) = {
    val Some( c1 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 1 ) )
    val Some( c2 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 0 ) )
    val Some( c3 ) = cs.find( x => ( x.antecedent.size == 0 ) && ( x.succedent.size == 1 ) )

    val y = Var( "y", Ti )
    val x0 = Var( "x0", Ti )
    val p = Const( "P", Ti -> ( Ti -> To ) )
    val y0 = Var( "Y0", Ti -> To )

    val s = c2.antecedent( 0 ) match { case HOLAtom( _, List( s, _ ) ) => s }

    val sub1 = Substitution( y0, Abs( y, HOLAtom( p, List( s, y ) ) ) )
    val sub2 = Substitution( x0, s )

    val r1 = RalInitial( c1 map { Set[LambdaExpression]() -> _ } )
    val r2 = RalInitial( c2 map { Set[LambdaExpression]() -> _ } )
    val r3 = RalInitial( c3 map { Set[LambdaExpression]() -> _ } )

    val r4 = RalSub( r1, sub1 )
    val r3a = RalSub( r3, sub2 )
    val r5 = RalCut( r3a, Seq( Suc( 0 ) ), r4, Seq( Ant( 0 ) ) )
    val r6 = RalCut( r5, Seq( Suc( 0 ) ), r2, Seq( Ant( 0 ) ) )
    r6
  }

  def refutation2( cs: Set[HOLSequent] ) = {
    val Some( c1 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 1 ) )
    val Some( c2 ) = cs.find( x => ( x.antecedent.size == 1 ) && ( x.succedent.size == 0 ) )
    val Some( c3 ) = cs.find( x => ( x.antecedent.size == 0 ) && ( x.succedent.size == 1 ) )

    val r1 = RalInitial( c1 map { Set[LambdaExpression]() -> _ } )
    val r2 = RalInitial( c2 map { Set[LambdaExpression]() -> _ } )
    val r3 = RalInitial( c3 map { Set[LambdaExpression]() -> _ } )

  }

  "Ceres_omega" should {
    "handle a proof with a manual refutation (1)" in {
      val ( p, cs, struct, proj ) = prepareProof( "llk/simple-leibnizeq.llk", "THEPROOF" )
      val rp = refutation1( cs )

      val ( acnf, _ ) = ceres_omega( proj, rp, sequentToLabelledSequent( p.root ), struct )
      val et = LKskToExpansionProof( acnf )
      ok
    }
  }

}
