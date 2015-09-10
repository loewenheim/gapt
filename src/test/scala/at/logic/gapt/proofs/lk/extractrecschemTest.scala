package at.logic.gapt.proofs.lk

import java.io.InputStreamReader
import java.util.zip.GZIPInputStream

import at.logic.gapt.algorithms.rewriting.DefinitionElimination
import at.logic.gapt.examples.Pi2Pigeonhole
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Utils
import at.logic.gapt.expr.hol.{ existsclosure, instantiate, univclosure }
import at.logic.gapt.formats.readers.XMLReaders.XMLReader
import at.logic.gapt.formats.xml.XMLParser.XMLProofDatabaseParser
import at.logic.gapt.grammars.{ HORS, HORule }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{ parseFormula, parseTerm }
import at.logic.gapt.proofs.{ Sequent, HOLSequent }
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.sat4j.Sat4jProver
import at.logic.gapt.provers.veriT.VeriTProver
import org.specs2.mutable._
import org.specs2.specification.core.Fragment

class ExtractRecSchemTest extends Specification {
  "simple" in {
    val P = FOLAtomHead( "P", 1 )
    val c = FOLConst( "c" )
    val f = FOLFunctionHead( "f", 1 )
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val z = FOLVar( "z" )

    val g0 = P( c )
    val g1 = All( y, P( y ) --> P( f( y ) ) )
    val g2 = P( f( f( f( f( c ) ) ) ) )

    val p1 = solve.solvePropositional(
      ( P( x ) --> P( f( x ) ) ) +:
        ( P( f( x ) ) --> P( f( f( x ) ) ) ) +:
        Sequent()
        :+ ( P( x ) --> P( f( f( x ) ) ) )
    ).get
    val cutf = All( z, P( z ) --> P( f( f( z ) ) ) )
    val p2 = ForallLeftRule( p1, P( x ) --> P( f( x ) ), g1, x )
    val p3 = ForallLeftRule( p2, P( f( x ) ) --> P( f( f( x ) ) ), g1, f( x ) )
    val p4 = ContractionMacroRule( p3 )
    val p5 = ForallRightRule( p4, P( x ) --> P( f( f( x ) ) ), cutf, x )

    val q1 = solve.solvePropositional(
      ( P( c ) --> P( f( f( c ) ) ) ) +:
        ( P( f( f( c ) ) ) --> P( f( f( f( f( c ) ) ) ) ) ) +:
        Sequent()
        :+ ( P( c ) --> P( f( f( f( f( c ) ) ) ) ) )
    ).get
    val q2 = ForallLeftRule( q1, P( c ) --> P( f( f( c ) ) ), cutf, c )
    val q3 = ForallLeftRule( q2, P( f( f( c ) ) ) --> P( f( f( f( f( c ) ) ) ) ), cutf, f( f( c ) ) )
    val q4 = ContractionMacroRule( q3 )

    val p = CutRule( p5, q4, cutf )

    val recSchem = extractRecSchem( p )
    val lang = recSchem.language( FOLAtom( "A" ) ).map( _.asInstanceOf[HOLFormula] )

    new Sat4jProver().isValid( lang ++: Sequent() ) must beTrue
  }

  "pi2 pigeonhole" in {
    val p9 = new Prover9Prover
    if ( !p9.isInstalled ) skipped

    val p = Pi2Pigeonhole()
    val recSchem = extractRecSchem( p )

    val lang = recSchem.language( FOLAtom( "A" ) ).map( _.asInstanceOf[HOLFormula] )

    p9.isValid( lang ++: Sequent() ) must beTrue
  }

  "tape proof" in {
    val pdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
    val proof = DefinitionElimination( pdb.Definitions, regularize( pdb.proof( "the-proof" ) ) )

    val recSchem = extractRecSchem( proof )

    val p9 = new Prover9Prover
    if ( !p9.isInstalled ) skipped

    val lang = recSchem.language( FOLAtom( "A", FOLConst( "n_0" ) ) ).map( _.asInstanceOf[HOLFormula] )
    // the following formulas are not present in the end-sequent...
    val additionalAxioms = existsclosure(
      "x+(y+z) = (x+y)+z" +:
        "x+y = y+x" +:
        "x != x+(y+1)" +:
        Sequent()
        map parseFormula
    )
    p9.isValid( lang ++: additionalAxioms ) must beTrue

    ok
  }

  "simple pi3" in {
    val cutf = parseFormula( "(all x (exists y (all z (P(x,y,z)))))" )

    var p1: LKProof = Axiom( parseFormula( "P(w1,w1,w2)" ) )
    p1 = ForallLeftBlock( p1, parseFormula( "(all x (all y (P(x,x,y))))" ), Seq( "w1", "w2" ) map parseTerm )
    p1 = ForallRightBlock( p1, instantiate( cutf, Seq( "w1", "w1" ) map parseTerm ), Seq( FOLVar( "w2" ) ) )
    p1 = ExistsRightBlock( p1, instantiate( cutf, Seq( "w1" ) map parseTerm ), Seq( FOLVar( "w1" ) ) )
    p1 = ForallRightBlock( p1, cutf, Seq( FOLVar( "w1" ) ) )

    var p2: LKProof = Axiom( parseFormula( "P(c,w3,d)" ) )
    p2 = ExistsRightBlock( p2, parseFormula( "(exists x (P(c,x,d)))" ), Seq( parseTerm( "w3" ) ) )
    p2 = ForallLeftBlock( p2, instantiate( cutf, Seq( "c", "w3" ) map parseTerm ), Seq( parseTerm( "d" ) ) )
    p2 = ExistsLeftRule( p2, instantiate( cutf, Seq( "c", "w3" ) map parseTerm ), FOLVar( "y" ), FOLVar( "w3" ) )
    p2 = ForallLeftBlock( p2, cutf, Seq( parseTerm( "c" ) ) )

    val p = CutRule( p1, p2, cutf )

    val recschem = extractRecSchem( p )
    println( recschem )
    recschem.language( FOLAtom( "A" ) ) foreach println
    recschem.rules map {
      case HORule( HOLAtom( head, _ ), _ ) => head
    } foreach { case Const( name, ty ) => println( s"$name: $ty" ) }

    new Sat4jProver().isValid(
      recschem.language( FOLAtom( "A" ) ).map( _.asInstanceOf[FOLFormula] ).toSeq ++: HOLSequent()
    ) must_== true
  }
}

class Pi2FactorialPOC extends Specification {
  val A = Const( "A", Ti -> To )
  val B = Const( "B", Ti -> ( Ti -> ( ( Ti -> To ) -> To ) ) )
  val C = Const( "C", Ti -> To )
  val D = Const( "D", ( Ti -> To ) -> ( Ti -> ( Ti -> ( Ti -> To ) ) ) )

  val O = Const( "0", Ti )
  val s = Const( "s", Ti -> Ti )
  val plus = Const( "+", Ti -> ( Ti -> Ti ) )
  val times = Const( "+", Ti -> ( Ti -> Ti ) )
  val g = Const( "g", Ti -> ( Ti -> Ti ) )
  val f = Const( "f", Ti -> Ti )

  val X = Var( "X", Ti -> To )
  val x = Var( "x", Ti )
  val y = Var( "y", Ti )
  val z = Var( "z", Ti )
  val w = Var( "w", Ti )

  val hors = HORS( Set(
    HORule( A( z ), B( z, s( O ), C ) ),
    HORule( A( z ), Eq( times( s( O ), z ), z ) ),
    HORule( A( z ), Neg( Eq( f( z ), g( s( O ), z ) ) ) ),
    HORule( C( w ), Top() ), // FIXME: NF != generated word
    HORule( B( s( x ), y, X ), B( x, times( y, s( x ) ), D( X, x, y ) ) ),
    HORule( D( X, x, y, w ), Eq( times( times( y, s( x ) ), w ), times( y, times( s( x ), w ) ) ) ),
    HORule( D( X, x, y, w ), Eq( g( y, s( x ) ), g( times( y, s( x ) ), x ) ) ),
    HORule( D( X, x, y, w ), Eq( f( s( x ) ), times( s( x ), f( x ) ) ) ),
    HORule( D( X, x, y, w ), X( times( s( x ), w ) ) ),
    HORule( B( O, y, X ), Eq( g( y, O ), y ) ),
    HORule( B( O, y, X ), Eq( f( O ), s( O ) ) ),
    HORule( B( O, y, X ), Eq( times( s( O ), s( O ) ), s( O ) ) ),
    HORule( B( O, y, X ), X( s( O ) ) )
  ) )

  def lang( i: Int ) = hors.language( A( Utils.numeral( i ) ) ).map( _.asInstanceOf[HOLFormula] )

  println( hors )
  println()
  lang( 3 ).toSeq.sortBy( _.toString ) foreach println
  println()

  "termination" in {
    lang( 10 )
    ok
  }

  "languages should be tautologies" in {
    val verit = new VeriTProver
    Fragment.foreach( 0 to 5 ) { i =>
      s"n = $i" in {
        if ( !verit.isInstalled ) skipped
        verit.isValid( lang( i ) ++: Sequent() ) must beTrue
      }
    }
  }
}