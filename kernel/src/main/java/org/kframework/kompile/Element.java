package org.kframework.kompile;

import java.util.*;

import org.kframework.kil.*;

public class Element implements GlobalElement {
	HashMap<NonTerminal, List<GlobalElement>> theMap;
	List<FunctionElement> functionDecls;
	List<GlobalElement> kResultProductions;
	Graph<NonTerminal> dataDependency;
	
	public Element(){
		theMap = new HashMap<NonTerminal, List<GlobalElement>>();
		functionDecls = new ArrayList<FunctionElement>();
		kResultProductions = new ArrayList<GlobalElement>();
		dataDependency = new Graph<NonTerminal>(true);
	}
	
	public void addKResult(GlobalElement result){
		this.kResultProductions.add(result);
	}
	
	public void addFunction(FunctionElement result){
		this.functionDecls.add(result);
	}
	
	public void addSort(NonTerminal key, GlobalElement result){
		if(this.theMap.containsKey(key)){
			this.theMap.get(key).add(result);
		} else {
			List<GlobalElement> resultList = new ArrayList<GlobalElement>();
			resultList.add(result);
			this.theMap.put(key, resultList);
		}
	}
	
	public void addToGraph(NonTerminal from, NonTerminal to){
		this.dataDependency.add(from);
		this.dataDependency.add(to);
		this.dataDependency.addArc(from, to, 1);
	}

	@Override
	public NonTerminal getResultSort() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List getSubSorts() {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public String getIsabelleLabel() {
		// TODO Auto-generated method stub
		return null;
	}
}
