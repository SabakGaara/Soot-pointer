package core;
import soot.toolkits.scalar.*;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.spark.ondemand.genericutil.Stack;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;

import java.util.*;

public class Analysis extends ForwardFlowAnalysis {
    Map<String, Set<String>> initSet;
    Map<Integer, Local> queries;
    String methodName;
    Set<Integer> allocIds;
    int allocId;
    Map<String, Set<String>> result;
    Map<String, Set<String>> returnSet;

    public Analysis(DirectedGraph _DG, String _methodName, Map<String, Set<String>> _initSet) {

        super(_DG);
        graph = _DG;
        allocId = 0;
        initSet = _initSet;
        methodName = _methodName;
        queries = new HashMap<Integer, Local>();
        result = new HashMap<String, Set<String>>();
//        argAndAlloc = new HashMap<Local, Set<Integer>>;
        returnSet = new HashMap<String, Set<String>>();
        allocIds = new HashSet<>();
        doAnalysis();
    }

    Set<String> getInvokeRet(Analysis invokeAnalysis, Map<String, Set<String>> out){
        Set<String> ret;
        ret = new HashSet<>();
        Map<String, Set<String>> tmpSet = invokeAnalysis.returnSet;
        ret = tmpSet.get("!ret");
        for (String argName: tmpSet.keySet()) {
            if (argName.startsWith("FR") || argName.startsWith("AR")) {
                out.put(argName, tmpSet.get(argName));
            }
        }
        Map<String, Set<String>> retResult = invokeAnalysis.result;
        for (String key: retResult.keySet()){
            if (result.containsKey(key)){
                result.get(key).addAll(retResult.get(key));
            }else{
                result.put(key, retResult.get(key));
            }
        }
        return ret;
    }

    Set<String> processInvokeFun(DirectedGraph graph, InvokeExpr ie, Map<String, Set<String>> in, Map<String, Set<String>> out){
        SootMethod m = ie.getMethod();
        graph = new ExceptionalUnitGraph(m.retrieveActiveBody());
        Set<String> retValSet = new HashSet<>();

        if (!m.getDeclaringClass().isJavaLibraryClass()) {


            Map<String, Set<String>> nextInitSet = new HashMap<String, Set<String>>();

            // 添加参数
            if (ie instanceof SpecialInvokeExpr) {
                String baseName = "LC"+((Local) ((SpecialInvokeExpr)ie).getBase()).getName();
                nextInitSet.put("TR", new HashSet<String>(in.get(baseName)));
            }
            List<Value> args = ie.getArgs();
            for (int i = 0; i < args.size(); i++) {
                Value curArg = args.get(i);
                if (curArg instanceof Local) {
                    String argName = "PR" +Integer.toString (i);
                    nextInitSet.put(argName, new HashSet<String>(in.get("LC"+((Local)curArg).getName())));
                }

                Map<String, Set<String>> tmpSet = in;
                for (String argName: tmpSet.keySet()) {
                    if (argName.startsWith("FR") || argName.startsWith("AR")) {
                        nextInitSet.put(argName, tmpSet.get(argName));
                    }
                }
            }
            String invokeMethodName =  m.getDeclaringClass().getName() + "." + m.getName();
            if (methodName.contains(invokeMethodName)){
                retValSet.clear();
                retValSet.add("unknown");
            }else {
                Analysis invokeAnalysis = new Analysis((graph), methodName + "->" + invokeMethodName, nextInitSet);
//            subAnalysis.printDetails();

                retValSet = getInvokeRet(invokeAnalysis, out);
            }

        }
    return retValSet;
    }

    protected void flowThrough(Object _in, Object _node, Object _out) {

        Map<String, Set<String>> in, out;
        in = (Map<String, Set<String>>) _in;
        out = (Map<String, Set<String>>) _out;
        Unit u = (Unit) _node;
        copy(in, out);
        Set<String> rVal = new HashSet<String>();;

        if (u instanceof InvokeStmt) {
            InvokeExpr ie = ((InvokeStmt) u).getInvokeExpr();
            if (ie.getMethod().toString().contains("Benchmark: void alloc")) {
                // 记录得到的new句ID
                allocId = ((IntConstant) ie.getArgs().get(0)).value;
                allocIds.add(allocId);
                return;
            }
            if (ie.getMethod().toString().contains("Benchmark: void test")) {
                int queryId = ((IntConstant) ie.getArgs().get(0)).value;
                Set<String> querySet = in.get("LC"+((Local) ie.getArgs().get(1)).getName());
                if (result.containsKey(Integer.toString(queryId))) {
                    result.get(Integer.toString(queryId)).addAll(querySet);
                } else{
                    result.put(Integer.toString(queryId), new TreeSet<String>(querySet));
                }
                return;
            }else{
                if (ie != null) {
                    SootMethod invokeMethod = ie.getMethod();
                    String methodSignature = invokeMethod.getSignature();
                    List<Value> invokeArgs = ie.getArgs();

                    if (ie instanceof InstanceInvokeExpr) {
                        // specialinvoke
                        // 跳过一些空函数，提高日志可读性
//                        if (methodSignature.contains("void <init>()")) return;
                        switch (methodSignature) {
                            case "<java.lang.Object: void <init>()>":
                                return;

                        }
                        if (methodSignature == methodName) {

                            rVal.add("unknown");
                            return;
                        }
                        rVal = processInvokeFun(graph, ie, in, out);
                    }
                }
            }
        }

        if (u instanceof IdentityStmt) {
            IdentityStmt is = (IdentityStmt) u;
            Value lop = is.getLeftOp();
            Value rop = is.getRightOp();
            if (rop instanceof ParameterRef) {
                // @parameter
                ParameterRef pr = (ParameterRef) rop;
                String prmName = "PR"+Integer.toString(pr.getIndex());
                Set<String> keys = in.keySet();
                for (String key: keys){
                    if (key.startsWith(prmName)){
//                        out.put("LC"+((Local) lop).getName(), in.get(key));
                        rVal.addAll(in.get(key));
                    }
                }
                if (rVal.isEmpty()){
                    rVal.add("unknown");
                }
            } else if (rop instanceof ThisRef) {
                // @this
                if (in.containsKey("TR")){
                    rVal = new HashSet<>(in.get("TR"));
                }else{
                    rVal.add("unknown");
                }


            }
            if (rVal != null) {
                if (lop instanceof Local) {
                    // 本地变量
                    String lName = ((Local) lop).getName();
                    if (!(((Local) lop).getName().contains("LC")))
                        lName = "LC" + lName;
                    out.put(lName, rVal);

                } else if (lop instanceof FieldRef) {
                    FieldRef rfref = (FieldRef) lop;
                    SootField rfield = rfref.getField();
                    String fieldName = rfield.getName();
                    if (lop instanceof InstanceFieldRef) {
                        // 实例 字段
                        InstanceFieldRef rifref = (InstanceFieldRef) lop;
                        Local rbase = (Local) rifref.getBase();
                        String baseName = "LC"+rbase.getName();

                        Set<String> baseVal = in.get(baseName);

                        for (String oneBaseVal:baseVal){
                            String baseFieldName = "FR"+oneBaseVal + ".FN" + fieldName;
                            if (baseVal.size() == 1) out.put(baseFieldName, rVal);
                            else{
                                if (!out.containsKey(baseFieldName)) out.put(baseFieldName, new HashSet<>());
                                out.get(baseFieldName).addAll(rVal);
                            }
                        }
                    }
                } else if (lop instanceof ArrayRef) {
                    // 数组元素
                    ArrayRef rref = (ArrayRef) lop;
                    Local rbase = (Local) rref.getBase();
                    String arrayName = "LC"+rbase.getName();

                    if (rref.getIndex() instanceof IntConstant) {
                        String arrayIndex = Integer.toString(((IntConstant) rref.getIndex()).value);

                        Set<String> arraySet = new HashSet<String>();
                        if (in.containsKey(arrayName)){
                            arraySet = in.get(arrayName);
                            for (String array:arraySet){
                                if (array.contains("unknown")) {
                                    continue;
                                }
                                String arrayRef = "AR"+array+".ID"+arrayIndex;
                                if (arraySet.size()==1){
                                    out.put(arrayRef, rVal);
                                }else{
                                    if (out.containsKey(arrayRef)){
                                        out.get(arrayRef).addAll(rVal);
                                    }else{
                                        out.put(arrayRef, rVal);
                                    }
                                }
                            }

                        }else{
                            out.put("AR"+rbase.getName()+".ID"+arrayIndex, rVal);
                        }

                    }
                } else {
                    // 其他左值
                }
            }
        } else if (u instanceof AssignStmt || u instanceof DefinitionStmt) {
            DefinitionStmt as = (DefinitionStmt) u;
            Value lop = as.getLeftOp();
            Value rop = as.getRightOp();

            if (rop instanceof AnyNewExpr) {
                if (allocId != 0){
                    rVal.add(Integer.toString(allocId));
                    allocId = 0;
                }else{
                    rVal.add("unknown");
                }
            } else if (rop instanceof Constant) {
                // 测评不需要处理非引用类型
                // rvar = scope.createVarBox(rop);
            } else if (rop instanceof Local) {
                String localName = "LC"+((Local)rop).getName();
                if (in.containsKey(localName)){
                    rVal = new HashSet<>(in.get(localName));
                }else{
                    rVal.add("unknown");
                }
            } else if (rop instanceof FieldRef) {
                FieldRef rfref = (FieldRef) rop;
                SootField rfield = rfref.getField();
                String fieldName = rfield.getName();
                if (rop instanceof InstanceFieldRef) {
                    // 实例 字段
                    InstanceFieldRef rifref = (InstanceFieldRef) rop;
                    Local rbase = (Local) rifref.getBase();
                    String baseName = "LC"+rbase.getName();

                    if (in.containsKey(baseName)){
                        Set<String> baseVal = in.get(baseName);
                        for (String oneBaseVal:baseVal){
                            if(oneBaseVal.contains("unknown")){
                                rVal.add("unknown");
                                continue;
                            }
                            String baseFieldName = "FR"+oneBaseVal + ".FN" + fieldName;
                            if (in.containsKey(baseFieldName)){
                                rVal.addAll(in.get(baseFieldName));
                            }else{
                                rVal.addAll(baseVal);
                            }
                        }
                    }else{
                        rVal.add("unknown");
                    }
                }
            } else if (rop instanceof ArrayRef) {
                // 数组元素
                ArrayRef rref = (ArrayRef) rop;
                Local rbase = (Local) rref.getBase();
                String arrayName = "LC"+rbase.getName();

                if (rref.getIndex() instanceof IntConstant) {
                    String arrayIndex = Integer.toString(((IntConstant) rref.getIndex()).value);
                    if (in.containsKey(arrayName)){
                        Set<String> arraySet = new HashSet<String>();
                        arraySet = in.get(arrayName);
                        for (String array:arraySet){
                            if (array.contains("unknown")){
                                rVal.add("unknown");
                                continue;
                            }
                            if (in.containsKey("AR"+array+".ID"+arrayIndex)){
                                rVal.addAll(in.get("AR"+array+".ID"+arrayIndex));
                            }else{
                                rVal.addAll(arraySet);
                            }
                        }
                    }
                }
            } else if (rop instanceof InvokeExpr){
                Set<String> reval = processInvokeFun(graph, (InvokeExpr)rop, in, out);
                if (reval!= null) {
                    rVal = reval;
                }
            }
            if (rVal != null) {
                if (lop instanceof Local) {
                    // 本地变量
                    String lName = ((Local) lop).getName();
                    if (!(((Local) lop).getName().contains("LC")))
                        lName = "LC" + lName;
                    out.put(lName, rVal);

                } else if (lop instanceof FieldRef) {
                    FieldRef rfref = (FieldRef) lop;
                    SootField rfield = rfref.getField();
                    String fieldName = rfield.getName();
                    if (lop instanceof InstanceFieldRef) {
                        // 实例 字段
                        InstanceFieldRef rifref = (InstanceFieldRef) lop;
                        Local rbase = (Local) rifref.getBase();
                        String baseName = "LC"+rbase.getName();

                        Set<String> baseVal = in.get(baseName);

                        for (String oneBaseVal:baseVal){
                            if (oneBaseVal.contains("unknown")){
                                continue;
                            }
                            String baseFieldName = "FR"+oneBaseVal + ".FN" + fieldName;
                            if (baseVal.size() == 1) out.put(baseFieldName, rVal);
                            else{
                                if (!out.containsKey(baseFieldName)) out.put(baseFieldName, new HashSet<>());
                                out.get(baseFieldName).addAll(rVal);
                            }
                        }

                    }
                } else if (lop instanceof ArrayRef) {
                    // 数组元素
                    ArrayRef rref = (ArrayRef) lop;
                    Local rbase = (Local) rref.getBase();
                    String arrayName = "LC"+rbase.getName();

                    if (rref.getIndex() instanceof IntConstant) {
                        String arrayIndex = Integer.toString(((IntConstant) rref.getIndex()).value);

                        Set<String> arraySet = new HashSet<String>();
                        if (in.containsKey(arrayName)){
                            arraySet = in.get(arrayName);
                            for (String array:arraySet){
                                if (array.contains("unknown")){
                                    continue;
                                }
                                String arrayRef = "AR"+array+".ID"+arrayIndex;
                                if (arraySet.size()==1){
                                    out.put(arrayRef, rVal);
                                }else{
                                    if (out.containsKey(arrayRef)){
                                        out.get(arrayRef).addAll(rVal);
                                    }else{
                                        out.put(arrayRef, rVal);
                                    }
                                }
                            }

                        }else{
                            out.put("AR"+rbase.getName()+".ID"+arrayIndex, rVal);
                        }

                    }
                } else {
                    // 其他左值
                }
            }
        } else if (u instanceof ReturnStmt || u instanceof ReturnVoidStmt) {
            Map<String, Set<String>> newReturnSet = new HashMap<String, Set<String>>();
            merge(returnSet, in, newReturnSet);
            returnSet = newReturnSet;


            if (u instanceof ReturnStmt) { // 处理非void函数对应的return语句
                Value retVal = ((ReturnStmt)u).getOp();
                if (retVal instanceof Local) {
                    if (!returnSet.containsKey("ret")) returnSet.put("ret", new HashSet<String>());
                    returnSet.get("ret").addAll(in.get("LC"+((Local)retVal).getName()));
                }

            }

            if (methodName == "main"){
                Set<String> queryIds = result.keySet();
                String strAnswer = "";
                for (String queryId :queryIds){
                    strAnswer += queryId + ":";
                    Set<String> answers = result.get(queryId);
                    for (String answer: answers){
                        strAnswer += "\t" + answer;
                    }
                    strAnswer += "\n";
                }
                AnswerPrinter.printAnswer(strAnswer);
            }

        } else {
            System.out.println("!!! " +methodName+ " Unit unknown: " + u.getClass().getName() + " [" + u.toString() + "]");
        }
    }


    @Override
    protected Object newInitialFlow() {
        return new HashMap<String, Set<String>>();
    }

    @Override
    protected void merge(Object o, Object a1, Object a2) {
        Map<String, Set<String>> a, b, c;
        a = (Map<String, Set<String>>) o;
        b = (Map<String, Set<String>>) a1;
        c = (Map<String, Set<String>>) a2;

        // 合并时针对对应变量，做Set上的并集
        // c = a 并 b
        c.clear(); c.putAll(a);
        for (Map.Entry<String, Set<String>> e: b.entrySet()) {
            if (!c.containsKey(e.getKey())) c.put(e.getKey(), new HashSet<String>());
            ((Set<String>) c.get(e.getKey())).addAll(e.getValue());
        }
    }

    protected Object entryInitialFlow() {
        Map<String, Set<String>> eif = new HashMap<>();
        copy(initSet, eif);
        return eif;
    }

    @Override
    protected boolean treatTrapHandlersAsEntries() {
        return super.treatTrapHandlersAsEntries();
    }

    protected void copy(Object _src, Object _dst) {
        Map<String, Set<String>> src, dst;
        src = (Map<String, Set<String>>) _src;
        dst = (Map<String, Set<String>>) _dst;

        dst.clear();
        for (Map.Entry<String, Set<String>> e : src.entrySet()) {
            dst.put(e.getKey(), new HashSet<String>(e.getValue()));
        }
    }

}
