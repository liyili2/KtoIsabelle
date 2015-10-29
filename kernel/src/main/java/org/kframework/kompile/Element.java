package org.kframework.kompile;

import java.util.*;
import org.kframework.kil.*;

public class Element implements GlobalElement {
	HashMap<NonTerminal, List<GlobalElement>> theMap;
	List<FunctionElement> functionDecls;
	List<GlobalElement> kResultProductions;
	
	public Element(){
		theMap = new HashMap<NonTerminal, List<GlobalElement>>();
		functionDecls = new ArrayList<FunctionElement>();
		kResultProductions = new ArrayList<GlobalElement>();
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

	@Override
	public NonTerminal getResultSort() {
		// TODO Auto-generated method stub
		return null;
	}
}
