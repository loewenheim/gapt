/** 
 * Description: 
**/

package at.logic.integration_tests

import _root_.at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import _root_.at.logic.algorithms.unification.{ACUEquality, MulACUEquality}
import _root_.at.logic.language.fol.{FOLExpression, FOLFormula}
import _root_.at.logic.language.lambda.typedLambdaCalculus.LambdaExpression
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.transformations.ceres.struct.{StructCreators, structToExpressionTree}
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.lk._
import at.logic.parsing.calculus.xml.saveXML
import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.writers.FileWriter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import java.io.{IOException, FileReader, FileInputStream, InputStreamReader}

/* comment out untill atp works again
import at.logic.provers.atp.Prover
import at.logic.provers.atp.commands._
import at.logic.provers.atp.refinements.UnitRefinement
*/
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.transformations.ceres.clauseSets.profile._

//import at.logic.calculi.resolution.robinson.Clause
import at.logic.algorithms.subsumption._
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.algorithms.fol.hol2fol._

import java.util.zip.GZIPInputStream
import java.io.File.separator

import scala.collection.mutable.Map

import at.logic.transformations.skolemization.skolemize
import at.logic.transformations.ceres.projections.Projections
import at.logic.parsing.language.tptp.TPTPFOLExporter

import at.logic.calculi.lk.base.types.FSequent
import at.logic.algorithms.fol.hol2fol._

import at.logic.provers.prover9._

private object MyAlg extends StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}

@RunWith(classOf[JUnitRunner])
class PrimeProofTest extends SpecificationWithJUnit {
  val box = List()
  def checkForProverOrSkip = Prover9.refute(box) must not(throwA[IOException]).orSkip

  def sequentToString( s: Sequent ) = {
    var ret = ""
    s.antecedent.foreach( formula => ret += formula.toStringSimple + ", ")
    ret += " :- "
    s.succedent.foreach( formula => ret += formula.toStringSimple + ", ")
    ret
  }

  def printStats( p: LKProof ) = {
    val stats = getStatistics( p )
    print("unary: " + stats.unary + "\n")
    print("binary: " + stats.binary + "\n")
    print("cuts: " + stats.cuts + "\n")
  }

  def mySort(x: Sequent, y: Sequent) = (x.toString < y.toString) // lexicographically

  "The system" should {

    def prime1(n: Int, refute: Boolean) = {
      checkForProverOrSkip

      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "prime1-" + n + ".xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2

      //val proof_sk = skolemize( regularize( proof )._1 )
      val proof_sk = skolemize( proof )
      val s = StructCreators.extract( proof_sk )

      // convert struct DAG to tree
      structToExpressionTree( s )

      val prf = deleteTautologies(proofProfile(s, proof_sk).map( _.toFSequent ))

      val tptp_prf = TPTPFOLExporter.tptp_problem( prf )
      val writer_prf = new java.io.FileWriter("target" + separator + "test-classes" + separator + "prime1-" + n + "-prf.tptp")
      writer_prf.write( tptp_prf )
      writer_prf.flush



      val cs_hol = deleteTautologies( StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent ) )

      def is_folsequent(fs : FSequent) = fs._1.forall(_.isInstanceOf[FOLFormula]) && fs._2.forall(_.isInstanceOf[FOLFormula])

      //val cs = cs_hol map ( (fs : FSequent) => FSequent(fs._1.map((x:HOLFormula) => reduceHolToFol(x)), fs._2.map((x:HOLFormula) => reduceHolToFol(x)) ) )
      def iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
      val cs = cs_hol map ( (fs : FSequent) => reduceHolToFol(fs, Map[LambdaExpression, ConstantStringSymbol](), iid) )
      println("# of non FOL formulas in cs =" + cs.filterNot(is_folsequent).size )

      val theory = new MulACUEquality(List("+", "*") map (new ConstantStringSymbol(_)), List("0", "1") map (new ConstantStringSymbol(_)))

      val subsumed = ACUEquality.apply_subsumptionalgorithm_to( (clause : FSequent, list : List[FSequent]) => list.exists( (x:FSequent) => MyAlg.subsumes(x, clause)), cs )

      val moduloclauses = ACUEquality.restricted_subsumption(theory, subsumed)



      println("Subsumed size = " + subsumed.size)
      println("Moduloclauses size = " + moduloclauses.size)

      val tptp = TPTPFOLExporter.tptp_problem( cs )
      val writer = new java.io.FileWriter("target" + separator + "test-classes" + separator + "prime1-" + n + "-cs.tptp")
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk )
      val path = "target" + separator + "test-classes" + separator + "prime1-" + n + "-sk.xml"

      val prf_cs_intersect = prf.filter(seq => cs.contains(seq))


      if (refute)
      {
        Prover9.refute( cs ) must beEqualTo( true )
        Prover9.refute( prf ) must beEqualTo( true )
      }

      saveXML( Pair("prime1-" + n + "-sk", proof_sk) ::
        projs.map( p => p._1 ).toList.zipWithIndex.map( p => Pair( "\\psi_{" + p._2 + "}", p._1 ) ),
        Pair("cs", cs)::Pair("prf",prf)::Pair("cs_prf_intersection", prf_cs_intersect)::Nil, path )
      (new java.io.File( path ) ).exists() must beEqualTo( true )
    }


    def euclid(n: Int) = {
      checkForProverOrSkip

      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "euclid-" + n + ".xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2

      //val proof_sk = skolemize( regularize( proof )._1 )
      val proof_sk = skolemize( proof )
      val s = StructCreators.extract( proof_sk )

      // convert struct DAG to tree
      structToExpressionTree( s )

      val prf = deleteTautologies(proofProfile(s, proof_sk).map( _.toFSequent ))

      val tptp_prf = TPTPFOLExporter.tptp_problem( prf )
      val writer_prf = new java.io.FileWriter("target" + separator + "test-classes" + separator + "euclid-" + n + "-prf.tptp")
      writer_prf.write( tptp_prf )
      writer_prf.flush



      val cs = deleteTautologies( StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs )
      val writer = new java.io.FileWriter("target" + separator + "test-classes" + separator + "euclid-" + n + "-cs.tptp")
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk )
      val path = "target" + separator + "test-classes" + separator + "euclid-" + n + "-sk.xml"

      val prf_cs_intersect = prf.filter(seq => cs.contains(seq))


      //Prover9.refute( cs ) must beEqualTo( true )
      //Prover9.refute( prf ) must beEqualTo( true )

      saveXML( Pair("euclid-" + n + "-sk", proof_sk) ::
        projs.map( p => p._1 ).toList.zipWithIndex.map( p => Pair( "\\psi_{" + p._2 + "}", p._1 ) ),
        Pair("cs", cs)::Pair("prf",prf)::Pair("cs_prf_intersection", prf_cs_intersect)::Nil, path )
      (new java.io.File( path ) ).exists() must beEqualTo( true )
    }

    //"parse, skolemize, and export the clause set in TPTP of the first-order prime proof (Euclid's proof), n=0" in euclid(0)

    //"parse, skolemize, and export the clause set in TPTP of the first-order prime proof (Euclid's proof), n=1" in euclid(1)

    //"parse, skolemize, and export the clause set in TPTP of the first-order prime proof (Euclid's proof), n=2" in euclid(2)

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof, n=0" in prime1(0, false)

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof, n=1" in prime1(1, false)

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof, n=2" in prime1(2, false)
     }
}