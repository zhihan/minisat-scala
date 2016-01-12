function [sat,sol] = SATSolver2(X, varargin)
% Solve SAT using minisat
s = my.sat.Solver;
[m,n]= size(X); % m : number of var, n: number of clause

v = zeros(1,m);  
for i=1:m+1
    v(i) = s.newVar(true); % Add decision variable
end

for i=1:n
    clause = X(:,i);
    num = length(find(clause));
    lits = javaArray('my.sat.Lit', num);
    pos = find(clause);
    for j=1:length(pos)
        if clause(pos(j)) > 0
            lits(j) = my.sat.Lit(pos(j), false);
        else
            lits(j) = my.sat.Lit(pos(j), true);
        end
    end
    a = s.addClause(lits);
    if ~a
        sat = false;
        return
    end
end

t = s.search(1000, 60);
if strcmp(char(t.toString), 'FALSE')
    sat = false;
elseif strcmp(char(t.toString), 'TRUE')
    sat = true;
end
sol = [];


end
