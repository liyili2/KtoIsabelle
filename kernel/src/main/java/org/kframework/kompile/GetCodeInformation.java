package org.kframework.kompile;

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
	
    public GlobalElement visit(Syntax node) throws RuntimeException {
    	
    	if(node.getPriorityBlocks().isEmpty()){
    		return new ThePair();
    	}
        
    	ThePair aPair = new ThePair();
    	aPair.add((NonTerminal)node.getChild(null),
    			(Production)(((PriorityBlock)(node.getPriorityBlocks().
    					get(0))).getProductions().get(0)));
    	return aPair;
    }
    
    public GlobalElement visit(Module node) throws RuntimeException {
    	
    	Element syntaxElement = new Element();
    	for(int i = 0; i < node.getItems().size(); ++i){
    		
    		if(node.getItems().get(i) instanceof Syntax){
    			GlobalElement aPair = this.visit((Syntax)node.getItems().get(i));
    			if(aPair instanceof ThePair){
    				syntaxElement.add(((ThePair)aPair).sort,
    						((ThePair)aPair).production);
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
