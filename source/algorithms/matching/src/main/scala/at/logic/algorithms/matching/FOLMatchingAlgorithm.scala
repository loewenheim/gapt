/*
 * FOLMatchingAlgorithm.scala
 *
 */
package at.logic.algorithms.matching

import at.logic.language.fol._

object FOLMatchingAlgorithm extends MatchingAlgorithm[FOLExpression] {
//object FOLMatchingAlgorithm {

  def matchTerm(term1: FOLExpression, term2: FOLExpression, restrictedDomain: List[FOLVar]) = matchSetOfTuples(restrictedDomain, (term1,term2)::Nil,Nil) match {
      case Some((Nil,ls)) => Some(Substitution(ls.map(x => (x._1.asInstanceOf[FOLVar],x._2))))
      case _ => None
    }

  def restrictSubstitution(delvars: List[FOLVar], sub: Substitution ): Substitution = {
    Substitution(sub.folmap.filter(pair => !delvars.contains(pair._1)))
  }


  def applySubToListOfPairs(l : List[(FOLExpression, FOLExpression)], s : Substitution) : List[(FOLExpression, FOLExpression)] = 
    return l.map(a => (s(a._1), s(a._2)))
  
  def createSubstFromListOfPairs(l: List[(FOLExpression, FOLExpression)]) : Substitution = {
    var sub = Substitution()
    for(x <- l) {
      sub = Substitution( sub.folmap + ( (x._1.asInstanceOf[FOLVar], x._2) ))
    }
    return sub
  }


  def matchSetOfTuples(moduloVarList: List[FOLVar], s1: List[(FOLExpression, FOLExpression)], s2 : List[(FOLExpression, FOLExpression)]) : Option[(List[(FOLExpression, FOLExpression)], List[(FOLExpression, FOLExpression)])] = (s1,s2) match {
    case (((a1,a2)::s), s2) if a1 == a2 => matchSetOfTuples(moduloVarList, s, s2)

    case ((FOLConst (name1),FOLConst (name2))::s,s2) if name1 != name2 => None
    case (((Function(f1,args1), Function(f2, args2)):: s), s2)
      if args1.length == args2.length && f1==f2  => {
          return matchSetOfTuples(moduloVarList, args1.zip(args2) ::: s, s2)
      }
    case ((Atom(f1,args1), Atom(f2, args2)):: s, s2)
      if args1.length == args2.length && f1==f2  => {
          return matchSetOfTuples(moduloVarList, args1.zip(args2) ::: s, s2)
      }
    case _ => matchSetOfTuples1(moduloVarList, s1, s2)
  }



  def matchSetOfTuples1(moduloVarList: List[FOLVar], s1: List[(FOLExpression, FOLExpression)], s2 : List[(FOLExpression, FOLExpression)]) : Option[(List[(FOLExpression, FOLExpression)], List[(FOLExpression, FOLExpression)])] = (s1,s2) match {
    case ((And(left1, right1), And(left2, right2)) ::s, s2) =>
      {
        return matchSetOfTuples(moduloVarList, (left1, left2) :: (right1, right2) :: s, s2)
      }
    case ((Or(left1, right1), Or(left2, right2)) ::s, s2) =>
      {
        return matchSetOfTuples(moduloVarList, (left1, left2) :: (right1, right2) :: s, s2)
      }
    case ((Imp(left1: FOLFormula, right1: FOLFormula), Imp(left2: FOLFormula, right2: FOLFormula)) ::s, s2) =>
      {
        return matchSetOfTuples(moduloVarList, (left1, left2) :: (right1, right2) :: s, s2)
      }
    case _ => matchSetOfTuples2(moduloVarList, s1, s2)
  }



  def matchSetOfTuples2(moduloVarList: List[FOLVar], s1: List[(FOLExpression, FOLExpression)], s2 : List[(FOLExpression, FOLExpression)]) : Option[(List[(FOLExpression, FOLExpression)], List[(FOLExpression, FOLExpression)])] = (s1,s2) match {
    case ((Neg(sub1), Neg(sub2)) ::s, s2) =>
      {
        return matchSetOfTuples(moduloVarList, (sub1, sub2) :: s, s2)
      }
    case ((AllVar(var1: FOLVar, sub1: FOLFormula), AllVar(var2: FOLVar, sub2: FOLFormula)) ::s, s2) =>
      {
        return matchSetOfTuples(var1::var2::moduloVarList, (sub1, sub2) :: s, s2)
      }
    case ((ExVar(var1: FOLVar, sub1: FOLFormula), ExVar(var2: FOLVar, sub2: FOLFormula)) ::s, s2) =>
      {
        return matchSetOfTuples(var1::var2::moduloVarList, (sub1, sub2) :: s, s2)
      }
    case _ => matchSetOfTuples3(moduloVarList, s1, s2)
  }


  def matchSetOfTuples3(moduloVarList: List[FOLVar], s1: List[(FOLExpression, FOLExpression)], s2 : List[(FOLExpression, FOLExpression)]) : Option[(List[(FOLExpression, FOLExpression)], List[(FOLExpression, FOLExpression)])] = 
  (s1,s2) match {
    case (((x : FOLVar,v)::s), s2) if !freeVariables(v).contains(x) && !moduloVarList.contains(x) =>
      val lst1 = applySubToListOfPairs(s, restrictSubstitution(moduloVarList, Substitution(Substitution(x,v).folmap)))
      val lst2 = applySubToListOfPairs(s2, restrictSubstitution(moduloVarList, Substitution(Substitution(x,v).folmap)))
      matchSetOfTuples(moduloVarList, lst1, (x,v)::lst2)

    case (((x : FOLVar,v)::s), s2) if !freeVariables(v).contains(x) && moduloVarList.contains(x)  =>
      {        
        if(createSubstFromListOfPairs(s2).apply(v) != createSubstFromListOfPairs(s2).map.get(x))
            return None
        return matchSetOfTuples(moduloVarList, s, s2)
      }


    case (((FOLConst (name1), x : FOLVar)::s), s2)  => None

    case (((y: FOLVar, x : FOLVar)::s), s2) if x!=y  => None

    case (Nil, s2) => Some((Nil, s2))
    case _ => None
  }
}
