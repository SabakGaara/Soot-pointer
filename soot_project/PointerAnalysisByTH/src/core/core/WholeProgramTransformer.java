package core;

import java.util.*;
import java.util.Map.Entry;

import soot.*;
import soot.jimple.DefinitionStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.queue.QueueReader;
import core.Anderson;
import core.AnswerPrinter;
import core.Analysis;

public class WholeProgramTransformer extends SceneTransformer {
	
	@Override
	protected void internalTransform(String arg0, Map<String, String> arg1) {

		SootMethod m = Scene.v().getMainMethod();


		Analysis pointerAnalysis = new Analysis(new ExceptionalUnitGraph(m.retrieveActiveBody()), "main" ,new HashMap<String, Set<String>>());
//		pointerAnalysis.printDetails();
//		Analysis.leaveMethod(m);

//		System.out.println("== with fallback ==\n" + AndersonAnalysis.getAnswer(true));
//		System.out.println("== without fallback ==\n" + AndersonAnalysis.getAnswer(false));
//		AnswerPrinter.printAnswer(AndersonAnalysis.getAnswer(true));
	}
}


