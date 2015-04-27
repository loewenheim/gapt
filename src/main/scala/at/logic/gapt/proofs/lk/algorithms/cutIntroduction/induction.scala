package at.logic.gapt.proofs.lk.algorithms.cutIntroduction

import at.logic.gapt.language.fol._
import at.logic.gapt.language.lambda.symbols.SymbolA
import Utils.numeral
import at.logic.gapt.provers.maxsat.{ MaxSat4j, MaxSATSolver }

object SipGrammar {
  type Production = ( FOLVar, FOLTerm )

  val tau = FOLVar( "τ" )
  val beta = FOLVar( "β" )
  val gamma = FOLVar( "γ" )
  val gammaEnd = FOLVar( "γ_end" )

  val alpha = FOLVar( "α" )
  val nu = FOLVar( "ν" )

  def gamma_i( i: Int ) = FOLVar( s"γ_$i" )

  def instantiate( prod: Production, n: Int ): Seq[Production] = prod match {
    case ( `tau`, r ) if freeVariables( r ).contains( beta ) =>
      Seq( tau -> FOLSubstitution( alpha -> numeral( n ), beta -> gamma_i( 0 ) )( r ) )
    case ( `tau`, r ) => ( 0 until n ) map { i =>
      tau ->
        FOLSubstitution( alpha -> numeral( n ), nu -> numeral( i ), gamma -> gamma_i( i + 1 ) )( r )
    }
    case ( `gamma`, r ) => ( 0 until n ) map { i =>
      gamma_i( i ) -> FOLSubstitution( alpha -> numeral( n ), nu -> numeral( i ), gamma -> gamma_i( i + 1 ) )( r )
    }
    case ( `gammaEnd`, r ) => Seq( gamma_i( n ) -> FOLSubstitution( alpha -> numeral( n ) )( r ) )
  }
}

case class SipGrammar( productions: Seq[SipGrammar.Production] ) {
  import SipGrammar._

  override def toString = s"{${productions map { case ( d, t ) => s"$d -> $t" } mkString ", "}}"

  def instanceGrammar( n: Int ) = {
    TratGrammar( tau, productions flatMap { p => instantiate( p, n ) } distinct )
  }
}

object normalFormsSipGrammar {
  type InstanceLanguage = ( Int, Seq[FOLTerm] )

  // TODO: better convention
  private def isFormulaSymbol( sym: SymbolA ) = sym.toString.startsWith( "tuple" )

  def apply( instanceLanguages: Seq[InstanceLanguage] ) = {
    import SipGrammar._
    val nfs = tratNormalForms( instanceLanguages flatMap ( _._2 ), Seq( gamma, alpha, nu ) )

    val prods = Set.newBuilder[Production]

    for ( nf <- nfs ) {
      val fv = freeVariables( nf )

      nf match {
        case FunctionOrConstant( f, _ ) if isFormulaSymbol( f ) =>
          if ( !fv.contains( nu ) ) prods += tau -> FOLSubstitution( gamma -> beta )( nf )
          prods += tau -> nf

        case _ =>
          prods += gamma -> nf
          if ( !fv.contains( nu ) && !fv.contains( gamma ) ) prods += gammaEnd -> nf
      }
    }

    SipGrammar( prods.result.toSeq )
  }
}

object atoms {
  def apply( f: FOLFormula ): Set[FOLFormula] = f match {
    case FOLAtom( _ )         => Set( f )
    case FOLAnd( x, y )       => apply( x ) union apply( y )
    case FOLOr( x, y )        => apply( x ) union apply( y )
    case FOLImp( x, y )       => apply( x ) union apply( y )
    case FOLNeg( x )          => apply( x )
    case FOLTopC | FOLBottomC => Set()
    case FOLExVar( x, y )     => apply( y )
    case FOLAllVar( x, y )    => apply( y )
  }
}

// TODO: only supports one instance language at the moment
case class SipGrammarMinimizationFormula( g: SipGrammar ) {
  def productionIsIncluded( p: SipGrammar.Production ) = FOLAtom( s"sp,$p" )

  def coversLanguageFamily( langs: Seq[normalFormsSipGrammar.InstanceLanguage] ) = {
    val cs = Seq.newBuilder[FOLFormula]
    langs foreach {
      case ( n, lang ) =>
        val tratMinForm = new GrammarMinimizationFormula( g.instanceGrammar( n ) ) {
          override def productionIsIncluded( p: TratGrammar.Production ) = FOLAtom( s"p,$n,$p" )
          override def valueOfNonTerminal( t: FOLTerm, a: FOLVar, rest: FOLTerm ) = FOLAtom( s"v,$n,$t,$a=$rest" )
        }
        val instanceCovForm = tratMinForm.coversLanguage( lang )
        cs += instanceCovForm

        val atomsInInstForm = atoms( instanceCovForm )

        ( for ( p <- g.productions; instP <- SipGrammar.instantiate( p, n ) )
          yield instP -> p ).groupBy( _._1 ).values foreach { l =>
          val tratProdInc = tratMinForm.productionIsIncluded( l.head._1 )
          if ( atomsInInstForm contains tratProdInc )
            cs += FOLImp( tratProdInc, FOLOr( l map ( _._2 ) map productionIsIncluded toList ) )
        }
    }
    FOLAnd( cs.result toList )
  }
}

object minimizeSipGrammar {
  def apply( g: SipGrammar, langs: Seq[normalFormsSipGrammar.InstanceLanguage], maxSATSolver: MaxSATSolver = new MaxSat4j ): SipGrammar = {
    val formula = SipGrammarMinimizationFormula( g )
    val hard = formula.coversLanguageFamily( langs )
    val atomsInHard = atoms( hard )
    val soft = g.productions map formula.productionIsIncluded filter atomsInHard.contains map ( FOLNeg( _ ) -> 1 )
    maxSATSolver.solveWPM( List( hard ), soft toList ) match {
      case Some( interp ) => SipGrammar(
        g.productions filter { p => interp.interpret( formula.productionIsIncluded( p ) ) } )
      case None => throw new TreeGrammarDecompositionException( "Grammar does not cover language." )
    }
  }
}

object findMinimalSipGrammar {
  def apply( langs: Seq[normalFormsSipGrammar.InstanceLanguage], maxSATSolver: MaxSATSolver = new MaxSat4j ) = {
    val polynomialSizedCoveringGrammar = normalFormsSipGrammar( langs )
    minimizeSipGrammar( polynomialSizedCoveringGrammar, langs, maxSATSolver )
  }
}