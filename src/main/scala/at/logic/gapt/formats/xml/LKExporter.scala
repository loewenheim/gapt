/*
 * LKExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats.xml

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.lksk.{ ExistsSkLeftRule, ExistsSkRightRule, ForallSkLeftRule, ForallSkRightRule, Axiom => LKskAxiom, WeakeningLeftRule => LKskWeakeningLeftRule, WeakeningRightRule => LKskWeakeningRightRule }

import scala.xml.dtd._

trait LKExporter extends HOLTermXMLExporter {
  //def exportSequent(seq : Sequent) = exportSequent(FSequent(seq))
  implicit def seq2fseq( s: OccSequent ) = s.toHOLSequent

  def exportSequent( seq: HOLSequent ) =
    <sequent>
      <formulalist>
        { seq.antecedent.map( exportTerm ) }
      </formulalist>
      <formulalist>
        { seq.succedent.map( exportTerm ) }
      </formulalist>
    </sequent>

  def exportSequentList( name: String, ls: List[HOLSequent] ) =
    <sequentlist symbol={ name }>
      { ls.map( x => exportSequent( x ) ) }
    </sequentlist>

  def exportProof( name: String, proof: LKProof ): scala.xml.Elem =
    <proof symbol={ name }>
      { exportProof( proof ) }
    </proof>

  // TODO: add permutation inferences! at the moment, the inferences are
  // not formally correct (when regarded as lists instead of multisets)
  //
  // TODO: distinguish first-/second-order quantifier inferences
  def exportProof( proof: LKProof ): scala.xml.Elem = proof match {
    // LKsk
    case LKskAxiom( seq )                              => <rule type="axiom"> { exportSequent( seq ) } </rule>
    case LKskWeakeningLeftRule( parent, seq, _ )       => <rule type="weakl"> { exportSequent( seq ) } { exportProof( parent ) } </rule>
    case LKskWeakeningRightRule( parent, seq, _ )      => <rule type="weakr"> { exportSequent( seq ) } { exportProof( parent ) } </rule>
    case ForallSkLeftRule( parent, seq, _, _, _ )      => <rule type="foralll"> { exportSequent( seq ) } { exportProof( parent ) } </rule>
    case ForallSkRightRule( parent, seq, _, _, _ )     => <rule type="forallr"> { exportSequent( seq ) } { exportProof( parent ) } </rule>
    case ExistsSkLeftRule( parent, seq, _, _, _ )      => <rule type="existsl"> { exportSequent( seq ) } { exportProof( parent ) } </rule>
    case ExistsSkRightRule( parent, seq, _, _, _ )     => <rule type="existsr"> { exportSequent( seq ) } { exportProof( parent ) } </rule>

    // LK
    case Axiom( seq )                                  => <rule type="axiom"> { exportSequent( seq ) } </rule>
    case WeakeningLeftRule( parent, seq, _ )           => exportUnaryRule( parent, seq, "weakl" )
    case WeakeningRightRule( parent, seq, _ )          => exportUnaryRule( parent, seq, "weakr" )
    case ContractionLeftRule( parent, seq, _, _, _ )   => exportUnaryRule( parent, seq, "contrr" )
    case ContractionRightRule( parent, seq, _, _, _ )  => exportUnaryRule( parent, seq, "contrl" )
    case AndLeft1Rule( parent, seq, _, _ )             => exportUnaryRule( parent, seq, "andl1" )
    case AndLeft2Rule( parent, seq, _, _ )             => exportUnaryRule( parent, seq, "andl2" )
    case OrRight1Rule( parent, seq, _, _ )             => exportUnaryRule( parent, seq, "orr1" )
    case OrRight2Rule( parent, seq, _, _ )             => exportUnaryRule( parent, seq, "orr2" )
    case ImpRightRule( parent, seq, _, _, _ )          => exportUnaryRule( parent, seq, "implr" )
    case NegLeftRule( parent, seq, _, _ )              => exportUnaryRule( parent, seq, "negl" )
    case NegRightRule( parent, seq, _, _ )             => exportUnaryRule( parent, seq, "negr" )
    case ForallLeftRule( parent, seq, _, _, _ )        => exportUnaryRule( parent, seq, "foralll" )
    case ExistsRightRule( parent, seq, _, _, _ )       => exportUnaryRule( parent, seq, "existsr" )
    case ForallRightRule( parent, seq, _, _, _ )       => exportUnaryRule( parent, seq, "forallr" )
    case ExistsLeftRule( parent, seq, _, _, _ )        => exportUnaryRule( parent, seq, "existsl" )
    case DefinitionLeftRule( parent, seq, _, _ )       => exportUnaryRule( parent, seq, "existsl" )
    case DefinitionRightRule( parent, seq, _, _ )      => exportUnaryRule( parent, seq, "defr" )

    case CutRule( p1, p2, seq, _, _ )                  => exportBinaryRule( p1, p2, seq, "cut" )
    case AndRightRule( p1, p2, seq, _, _, _ )          => exportBinaryRule( p1, p2, seq, "andr" )
    case OrLeftRule( p1, p2, seq, _, _, _ )            => exportBinaryRule( p1, p2, seq, "orl" )
    case ImpLeftRule( p1, p2, seq, _, _, _ )           => exportBinaryRule( p1, p2, seq, "impll" )
    case EquationLeft1Rule( p1, p2, seq, _, _, _, _ )  => exportBinaryRule( p1, p2, seq, "eql1" )
    case EquationLeft2Rule( p1, p2, seq, _, _, _, _ )  => exportBinaryRule( p1, p2, seq, "eql2" )
    case EquationRight1Rule( p1, p2, seq, _, _, _, _ ) => exportBinaryRule( p1, p2, seq, "eqr1" )
    case EquationRight2Rule( p1, p2, seq, _, _, _, _ ) => exportBinaryRule( p1, p2, seq, "eqr2" )
  }

  def exportUnaryRule( parent: LKProof, conc: OccSequent, rt: String ) =
    <rule type={ rt }> { exportSequent( conc ) } { exportProof( parent ) } </rule>

  def exportBinaryRule( p1: LKProof, p2: LKProof, conc: OccSequent, rt: String ) =
    <rule type={ rt }> { exportSequent( conc ) } { exportProof( p1 ) } { exportProof( p2 ) } </rule>
}

object saveXML {
  def apply( ls: List[LKProof], names: List[String], outputFile: String )( implicit dummyImplicit: DummyImplicit ): Unit = {
    val exporter = new LKExporter {}
    val pairs = ls.zip( names )
    scala.xml.XML.save(
      outputFile,
      <proofdatabase>
        <definitionlist/>
        <axiomset/>{ pairs.map( p => exporter.exportProof( p._2, p._1 ) ) }<variabledefinitions/>
      </proofdatabase>, "UTF-8", true,
      scala.xml.dtd.DocType( "proofdatabase", scala.xml.dtd.SystemID( "http://www.logic.at/ceres/xml/5.0/proofdatabase.dtd" ), Nil )
    )
  }

  def apply( proofs: List[Tuple2[String, LKProof]], sequentlists: List[Tuple2[String, List[HOLSequent]]], filename: String ): Unit =
    {
      val exporter = new LKExporter {}
      val p_xmls = proofs.map( p => exporter.exportProof( p._1, p._2 ) )
      val s_xmls = sequentlists.map( p => exporter.exportSequentList( p._1, p._2 ) )
      val output =
        <proofdatabase>
          <definitionlist/>
          <axiomset/>
          { p_xmls }
          { s_xmls }
          <variabledefinitions/>
        </proofdatabase>
      scala.xml.XML.save( filename, output, "UTF-8", true,
        DocType( "proofdatabase", SystemID( "http://www.logic.at/ceres/xml/5.0/proofdatabase.dtd" ), Nil ) )
    }
}
