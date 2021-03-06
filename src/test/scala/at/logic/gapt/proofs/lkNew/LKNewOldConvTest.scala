package at.logic.gapt.proofs.lkNew

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.proofs.lk.base._
import org.specs2.mutable._

import scala.io.Source

class LKNewOldConvTest extends Specification {

  def load( fn: String ) =
    Prover9Importer.lkProof(
      Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( fn ) ).mkString
    )

  if ( !Prover9Importer.isInstalled ) args( skipAll = true )

  "GEO037m4" in {

    val n = load( "GEO037-2.out" )
    val o = lkNew2Old( n )
    val n_ = lkOld2New( o )
    n.endSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
    n_.endSequent must beSyntacticFSequentEqual( n.endSequent )
  }

  "goat puzzle" in {

    val n = load( "PUZ047+1.out" )
    val o = lkNew2Old( n )
    val n_ = lkOld2New( o )
    n.endSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
    n_.endSequent must beSyntacticFSequentEqual( n.endSequent )
  }

  "cade1example.out" in {

    val n = load( "cade13example.out" )
    val o = lkNew2Old( n )
    val n_ = lkOld2New( o )
    n.endSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
    n_.endSequent must beSyntacticFSequentEqual( n.endSequent )
  }

  "proof with new_symbol" in {

    val n = load( "ALG138+1.out" )
    val o = lkNew2Old( n )
    val n_ = lkOld2New( o )
    n.endSequent must beSyntacticFSequentEqual( o.root.toHOLSequent )
    n_.endSequent must beSyntacticFSequentEqual( n.endSequent )
  }

}
