package soot.toolkits.scalar;

import soot.Local;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.toolkits.graph.UnitGraph;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

// follow the chain flow and and build variable trace map. e.g. what variable stays in slot after previous
// assignment
// functionality similar to SimpleLiveLocals but considers slot variables only
public class RoboVmLiveSlotLocals {
    private final UnitGraph graph;
    private final Map<Unit, Map<Integer, Local>> localVisibility = new HashMap<>();


    public RoboVmLiveSlotLocals(UnitGraph graph) {
        this.graph = graph;
        traverseNodes(graph.getHeads());
    }

    public Map<Integer, Local> getLocalsBeforUnit(Unit u) {
        return localVisibility.get(u);
    }

    private void traverseNodes(List<Unit> units) {
        Set<Unit> visitedUnits = new HashSet<>();
        Deque<Pair<Iterator<Unit>, Map<Integer, Local>>> stack = new ArrayDeque<>();
        stack.push(new Pair<>(units.iterator(), new HashMap<>()));

        while (!stack.isEmpty()) {
            Pair<Iterator<Unit>, Map<Integer, Local>> pair = stack.pop();
            Iterator<Unit> it = pair.o1;
            Map<Integer, Local> definedLocals = pair.o2;

            while (it.hasNext()) {
                Unit u = it.next();

                if (visitedUnits.contains(u))
                    continue;
                visitedUnits.add(u);
                localVisibility.put(u, definedLocals);

                // no need to resolve this unit variables if there is no successors of it, e.g. nobody will see these
                // variables
                List<Unit> successors = graph.getSuccsOf(u);
                if (successors == null || successors.isEmpty())
                    continue;

                // don't bother if there is one successor and it was processed
                if (successors.size() == 1 && visitedUnits.contains(successors.get(0)))
                    continue;

                // modify locals  unit does declare
                Map<Integer, Local> unitLocals = definedLocals;
                if (u.getDefBoxes().size() == 1) {
                    ValueBox loBox = u.getDefBoxes().get(0);
                    Value lo = loBox.getValue();
                    Local local = null;
                    if (lo instanceof Local)
                        local = (Local) lo;
                    if (local != null && local.getIndex() >= 0) {
                        // definition of local
                        unitLocals = new HashMap<>(definedLocals);
                        unitLocals.put(local.getIndex(), local);
                    }
                }

                // push unit to stack, reuse current position if this unit is last of successors
                if (it.hasNext()) {
                    // save actual step in stack
                    stack.push(new Pair<>(it, definedLocals));
                }

                // start processing successors
                definedLocals = unitLocals;
                it = successors.iterator();
            }
        }
    }
}
