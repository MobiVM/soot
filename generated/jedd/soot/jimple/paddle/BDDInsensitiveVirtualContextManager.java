package soot.jimple.paddle;

import soot.jimple.paddle.queue.*;
import soot.jimple.paddle.bdddomains.*;
import soot.*;

public class BDDInsensitiveVirtualContextManager extends AbsVirtualContextManager {
    BDDInsensitiveVirtualContextManager(Rctxt_var_obj_srcm_stmt_kind_tgtm in, Qsrcc_srcm_stmt_kind_tgtc_tgtm out) {
        super(in, out);
    }
    
    public boolean update() {
        final jedd.internal.RelationContainer newOut =
          new jedd.internal.RelationContainer(new jedd.Attribute[] { srcc.v(), srcm.v(), stmt.v(), kind.v(), tgtc.v(), tgtm.v() },
                                              new jedd.PhysicalDomain[] { C1.v(), MS.v(), ST.v(), KD.v(), C2.v(), MT.v() },
                                              ("<soot.jimple.paddle.bdddomains.srcc:soot.jimple.paddle.bdddo" +
                                               "mains.C1, soot.jimple.paddle.bdddomains.srcm:soot.jimple.pad" +
                                               "dle.bdddomains.MS, soot.jimple.paddle.bdddomains.stmt:soot.j" +
                                               "imple.paddle.bdddomains.ST, soot.jimple.paddle.bdddomains.ki" +
                                               "nd:soot.jimple.paddle.bdddomains.KD, soot.jimple.paddle.bddd" +
                                               "omains.tgtc:soot.jimple.paddle.bdddomains.C2, soot.jimple.pa" +
                                               "ddle.bdddomains.tgtm:soot.jimple.paddle.bdddomains.MT> newOu" +
                                               "t = jedd.internal.Jedd.v().join(jedd.internal.Jedd.v().read(" +
                                               "jedd.internal.Jedd.v().project(in.get(), new jedd.PhysicalDo" +
                                               "main[...])), jedd.internal.Jedd.v().literal(new java.lang.Ob" +
                                               "ject[...], new jedd.Attribute[...], new jedd.PhysicalDomain[" +
                                               "...]), new jedd.PhysicalDomain[...]); at /home/research/ccl/" +
                                               "olhota/olhotak/soot-trunk/src/soot/jimple/paddle/BDDInsensit" +
                                               "iveVirtualContextManager.jedd:35,45-51"),
                                              jedd.internal.Jedd.v().join(jedd.internal.Jedd.v().read(jedd.internal.Jedd.v().project(in.get(),
                                                                                                                                     new jedd.PhysicalDomain[] { V1.v(), C1.v(), H1.v() })),
                                                                          jedd.internal.Jedd.v().literal(new Object[] { null, null },
                                                                                                         new jedd.Attribute[] { srcc.v(), tgtc.v() },
                                                                                                         new jedd.PhysicalDomain[] { C1.v(), C2.v() }),
                                                                          new jedd.PhysicalDomain[] {  }));
        out.add(new jedd.internal.RelationContainer(new jedd.Attribute[] { kind.v(), srcm.v(), stmt.v(), srcc.v(), tgtc.v(), tgtm.v() },
                                                    new jedd.PhysicalDomain[] { KD.v(), MS.v(), ST.v(), C1.v(), C2.v(), MT.v() },
                                                    ("out.add(newOut) at /home/research/ccl/olhota/olhotak/soot-tr" +
                                                     "unk/src/soot/jimple/paddle/BDDInsensitiveVirtualContextManag" +
                                                     "er.jedd:38,8-11"),
                                                    newOut));
        return !jedd.internal.Jedd.v().equals(jedd.internal.Jedd.v().read(newOut), jedd.internal.Jedd.v().falseBDD());
    }
}