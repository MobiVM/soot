package soot.toolkits.scalar;

import soot.Body;
import soot.BodyTransformer;
import soot.BooleanType;
import soot.ByteType;
import soot.CharType;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.LocalVariable;
import soot.ShortType;
import soot.Singletons;
import soot.Type;
import soot.Unit;
import soot.ValueBox;
import soot.coffi.Util;
import soot.jimple.GroupIntPair;
import soot.jimple.IdentityStmt;
import soot.jimple.ParameterRef;
import soot.jimple.toolkits.typing.fast.Integer127Type;
import soot.jimple.toolkits.typing.fast.Integer1Type;
import soot.jimple.toolkits.typing.fast.Integer32767Type;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.Chain;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;


/**
 *    A BodyTransformer that attemps to merge back Locals that have same local index and same type
 *    It has to be called after TypeAssigner
 */
public class RoboVmLocalPacker extends BodyTransformer
{
    public RoboVmLocalPacker(Singletons.Global g ) {}
    public static RoboVmLocalPacker v() { return G.v().soot_toolkits_scalar_RoboVmLocalPacker(); }

    protected void internalTransform(Body body, String phaseName, Map options)
    {
        if(Options.v().verbose())
            G.v().out.println("[" + body.getMethod().getName() + "] RoboVm Packing locals...");

        if (!body.getLocalVariables().isEmpty()) {
            // promote integer types -- this happens after variable split
            promoteIntTypes(body);
        }


        // replacement map -- contain map of one local to another in case it is subject for replacement
        Map<Local, Local> replacements = new HashMap<>();

        // merge locals and stack variables
        mergeVariables(body, replacements);
//        mergeLocalVariables(body, replacements);
//
//        // merge stack variables (similar to one done in LocalPacker)
//        mergeStackVariables(body, replacements);

        // do replacements -- pack
        if (!replacements.isEmpty()) {
            // Go through all valueBoxes of this method and perform changes
            for (Unit s : body.getUnits()) {
                for (ValueBox box : s.getUseBoxes()) {
                    if (box.getValue() instanceof Local) {
                        Local l = (Local) box.getValue();
                        Local r = replacements.get(l);
                        if (r != null)
                            box.setValue(r);
                    }
                }
                for (ValueBox box : s.getDefBoxes()) {
                    if (box.getValue() instanceof Local) {
                        Local l = (Local) box.getValue();
                        Local r = replacements.get(l);
                        if (r != null)
                            box.setValue(r);
                    }
                }
            }

            // update body locals (remove one that were replaced)
            List<Local> oldLocals = new ArrayList<>(body.getLocals());
            body.getLocals().clear();
            for (Local l : oldLocals) {
                if (!replacements.containsKey(l))
                    body.getLocals().add(l);
            }
        }
    }

    /**
     * perform boolean/byte/short type promotion if required as soot will try to assign as smaller type as
     * possible, check local variable type against one stored in debug variable information section
     * this is required for successful packing as only variables of one type and slot will get packed
     */
    private void promoteIntTypes(Body body) {
        Chain<Unit> units = body.getUnits();

        // follow the chain flow and and build variable trace map. e.g. what variable stays in slot after previous
        // assignment
        RoboVmLiveSlotLocals liveSlotLocals = new RoboVmLiveSlotLocals(new ExceptionalUnitGraph(body));

        // find all parameters
        Map<Integer, Unit> paramDefinitions = new HashMap<>();
        for (Unit s : units) {
            if (s instanceof IdentityStmt && ((IdentityStmt)s).getRightOp() instanceof ParameterRef)
            {
                IdentityStmt is = (IdentityStmt)s;
                if (is.getLeftOpBox().getValue() instanceof Local) {
                    Local l = (Local) is.getLeftOpBox().getValue();
                    if (l.getIndex() >= 0)
                        paramDefinitions.put(l.getIndex(), s);
                }
            }
        }

        // perform int/boolean type promotion up to debug information available
        // move through debug information and consider only variables of int types
        for (LocalVariable v : body.getLocalVariables()) {
            // skip all technical variables that contains $ as these are source of trouble in kotlin case
            if (v.getName().contains("$"))
                continue;

            int varSizeBits = getVariableSize(v.getDescriptor());
            if (varSizeBits < 0)
                continue; // not integer

            // move through units to check this associated with it variables
            Unit startUnit = paramDefinitions.get(v.getIndex());
            if (startUnit == null)
                startUnit = v.getStartUnit();
            Unit endUnit = v.getEndUnit();
            if (endUnit != null) {
                // end unit is exclusive
                if (endUnit != startUnit)
                    endUnit = units.getPredOf(endUnit);
            } else {
                endUnit = units.getLast();
            }

            Iterator<Unit> it = units.iterator(startUnit, endUnit);
            while (it.hasNext()) {
                Unit u = it.next();
                Map<Integer, Local> unitLocals = liveSlotLocals.getLocalsBeforUnit(u);
                Local varLocal = unitLocals != null ? unitLocals.get(v.getIndex()) : null;
                if (varLocal != null) {
                    int localSizeBits = getVariableSize(varLocal.getType());
                    if (localSizeBits < 0) {
                        // it shall not happen but possible in case debug information is broken
                        // often happen with kotlin classes and auto-generated variables
                        // throw new Error();
                    } else if(localSizeBits < varSizeBits) {
                        // promote type it
                        varLocal.setType(toType(v.getDescriptor()));
                    }
                } else {
                    if (u != startUnit) {
                        // such local not found, strange !
                        // throw new Error();
                    }
                }
            }
        }
    }

    private void mergeVariables(Body body, Map<Local, Local> replacements) {
        Map<Local, Object> localToGroup = new HashMap<>();
        // A group represents a bunch of locals which may potentially intefere with each other
        // 2 separate groups can not possibly interfere with each other
        // (coloring say ints and doubles)

        Map<Object, Integer> groupToColorCount = new HashMap<>();
        Map<Local, Integer> localToColor = new HashMap<>();

        // Assign each local to a group, and set that group's color count to 0.
        for (Local l : body.getLocals()) {
            // get type of variable
            // stack can be merger withing them selfs without any constrains just base on type
            // locals can be merged only if type and index matches, so create a special type for it
            // using group int pair for this purpose as type
            Object localType = l.getIndex() < 0 ? l.getType() : new GroupIntPair(l.getType(), l.getIndex());
            localToGroup.put(l, localType);

            if (!groupToColorCount.containsKey(localType))
                groupToColorCount.put(localType, 0);
        }

        // Call the graph colorer.
        FastColorer.assignColorsToLocals(body, localToGroup, localToColor, groupToColorCount);

        // Map each local to a new local.
        Map<GroupIntPair, Local> groupIntToLocal = new HashMap<>();
        for (Local local : body.getLocals()) {
            Object group = localToGroup.get(local);
            int color = localToColor.get(local);
            GroupIntPair pair = new GroupIntPair(group, color);

            if (groupIntToLocal.containsKey(pair)) {
                replacements.put(local, groupIntToLocal.get(pair));
            } else {
                groupIntToLocal.put(pair, local);
            }
        }
    }

    private int getVariableSize(String descriptor) {
        switch (descriptor) {
            case "Z":
                return 1;
            case "B":
                return 8;
            case "C":
                return 16;
            case "S":
                return 16;
            case "I":
                return 32;
        }

        return -1;
    }

    private int getVariableSize(Type type) {
        if (type instanceof Integer1Type)
            return 1;
        if (type instanceof BooleanType)
            return 1;
        if (type instanceof Integer127Type)
            return 8;
        if (type instanceof ByteType)
            return 8;
        if (type instanceof ShortType)
            return 16;
        if (type instanceof CharType)
            return 16;
        if (type instanceof Integer32767Type)
            return 32;
        if (type instanceof IntType)
            return 32;

        return -1;
    }

    private Type toType(String descriptor) {
        return Util.v().jimpleTypeOfFieldDescriptor(descriptor);
    }
}

