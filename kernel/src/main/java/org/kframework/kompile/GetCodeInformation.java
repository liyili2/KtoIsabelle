package org.kframework.kompile;

import java.util.ArrayList;
import java.util.Set;

import org.kframework.kil.loader.Context;
import org.kframework.kil.*;

public class GetCodeInformation
          extends AbstractVisitor<Void, GlobalElement, RuntimeException> {

	public GetCodeInformation(Context context) {
		super(context);
		// TODO Auto-generated constructor stub
	}
	
	
	public GlobalElement visit(Definition node) {
        
		return this.visit((Module)(node.getItems().get(0)));		
	}
	
	private String generateKLabel(Production item){
		String label = "'";
		for(ProductionItem p : item.getItems()){
			if(!(p instanceof Terminal)){
				label += "_";
			} else {
				label += ((Terminal)p).getTerminal();
			}
		}
		return label;
	}
	
    public GlobalElement visit(Syntax node) throws RuntimeException {
    	
    	if(node.getPriorityBlocks().isEmpty()){
    		return new ThePair();
    	}
    	Set<Production> prods = node.getSyntaxByTag("function", context);
    	ArrayList<Production> items = new ArrayList<Production>(prods);
    	if(!prods.isEmpty()){
    		ArrayList<NonTerminal> arguments = new ArrayList<NonTerminal>();
    		for(int i = 0; i < items.get(0).getItems().size(); ++i){
    			if(items.get(0).getItems().get(i) instanceof NonTerminal){
    				arguments.add((NonTerminal) items.get(0).getItems().get(i));
    			}
    		}
    		FunctionElement result =
    				new FunctionElement(generateKLabel(items.get(0)),arguments,node.getChild(null));
    		return result;
    	} else {
    		ThePair aPair = new ThePair();
        	aPair.add((NonTerminal)node.getChild(null),
        			(Production)(((PriorityBlock)(node.getPriorityBlocks().
        					get(0))).getProductions().get(0)));
        	return aPair;
    	}
    }
    
    public GlobalElement visit(Module node) throws RuntimeException {
    	
    	Element syntaxElement = new Element();
    	for(int i = 0; i < node.getItems().size(); ++i){
    		
    		if(node.getItems().get(i) instanceof Syntax){
    			GlobalElement aPair = this.visit((Syntax)node.getItems().get(i));
    			if(aPair instanceof ThePair){
    				syntaxElement.add(((ThePair)aPair).sort,
    						((ThePair)aPair).production);
    			} else if(aPair instanceof FunctionElement){
    				syntaxElement.add(((FunctionElement)aPair).klabel
    						, ((FunctionElement)aPair).arguments, ((FunctionElement)aPair).result);
    			}
    		}
    	}
    	return syntaxElement;
    }

    @Override
	public GlobalElement defaultReturnValue(ASTNode node, Void p) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <T extends ASTNode> T processChildTerm(T child,
			GlobalElement childResult) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean visitChildren() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean cache() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public <T extends ASTNode> T copy(T original) {
		// TODO Auto-generated method stub
		return null;
	}

}
