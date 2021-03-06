
package at.logic.gapt.provers.basicProver

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.provers.Prover

/** Uses our propositional prover to get LK proof andsat4j for validity check */
object BasicProver extends Prover {
  def getLKProof( seq: HOLSequent ): Option[LKProof] = LKProver getLKProof seq
  override def isValid( seq: HOLSequent ): Boolean = Sat4j isValid seq
}
