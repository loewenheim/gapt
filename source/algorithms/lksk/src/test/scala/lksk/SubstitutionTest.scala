/** 
 * Description: 
**/

package at.logic.algorithms.lksk

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher


import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lksk._
import at.logic.calculi.lksk.base.TypeSynonyms._
import at.logic.calculi.lksk.base._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions.Substitution


class SubstitutionTest extends SpecificationWithJUnit {
  "Substitutions" should {
    val f = HOLConst(new ConstantStringSymbol("f"), i -> i)
    val y = HOLVar("y", i)
    val x = HOLVar("x", i)
    val a = HOLVar("a", i)
    val fa = HOLApp(f, a)
    val Rafa = Atom("R", a::fa::Nil)
    val exyRay = ExVar(y, Atom("R", a::y::Nil ))
    val allxexy = AllVar(x, ExVar( y, Atom( "R", x::y::Nil ) ) )

    val ax = Axiom(Sequent(Rafa::Nil, Rafa::Nil), Pair( (EmptyLabel() + a)::Nil , EmptyLabel()::Nil ) )
    val r1 = ExistsSkLeftRule(ax._1, ax._2._1.first, exyRay, fa)
    val r2 = ForallSkLeftRule(r1, r1.prin.first, allxexy, a, true)
    r2.root.antecedent.toList.first must beLike {case o: LabelledFormulaOccurrence => o.label == EmptyLabel()}
    r2.root.succedent.toList.first must beLike {case o: LabelledFormulaOccurrence => o.label == EmptyLabel()}

    "work for an axiom" in {
      val Px = Atom("P", x::Nil)
      val c : HOLExpression = HOLConst(new ConstantStringSymbol("c"), i)
      val Pc = Atom("P", c::Nil)

      val a = Axiom( Sequent( Px::Nil, Px::Nil ), Pair( (EmptyLabel() + x)::Nil, (EmptyLabel() + y)::Nil ) )
      val subst = Substitution(x, c)
      val r = applySubstitution(a._1, subst)
      r._1.root.antecedent.toList.first must beLike {case o : LabelledFormulaOccurrence => o.label == (EmptyLabel() + c) && o.formula == Pc }
      r._1.root.succedent.toList.first must beLike {case o : LabelledFormulaOccurrence => o.label == (EmptyLabel() + y) && o.formula == Pc }
    }

    "apply correctly to a simple proof" in {
      val c = HOLConst(new ConstantStringSymbol("c"), i)
      val g = HOLConst(new ConstantStringSymbol("g"), i -> i)
      val gc = HOLApp(g, c)
      val fgc = HOLApp(f, gc)
      val Rgcfgc = Atom("R", gc::fgc::Nil )
      val exyRgcy = ExVar(y, Atom( "R", gc::y::Nil ) )
      val subst = Substitution[HOLExpression]( a, gc ) // a <- g(c)

      val p_s = applySubstitution( r2, subst )
      p_s._1.root.antecedent.toList.first must beLike{ case o : LabelledFormulaOccurrence => o.label == EmptyLabel() && o.formula == allxexy }
    p_s._1.root.succedent.toList.first must beLike{ case o : LabelledFormulaOccurrence => o.label == EmptyLabel() && o.formula == Rgcfgc }
    }
  }
}
