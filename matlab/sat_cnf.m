function [sat, sol, X] = sat_cnf(cnffile, varargin)
    fid = fopen(cnffile);
    if fid<0
        return
    end
    k=1;
    while ~feof(fid)
        tline = fgetl(fid);
        tline = strtrim(tline);
        if isempty(tline)
            continue;
        end
        if (tline(1)=='p' || tline(1)=='P')
            st = regexpi(tline, 'cnf');
            dim = str2num(tline(st+3:end));
            X = sparse(dim(1), dim(2));
            continue
        end
        
        if (tline(1)~= 'c') % discard comments
            x = str2num(tline);
            for i=1:length(x)-1
                v = x(i);
                if v>0
                    X(v,k) = 1;
                elseif v<0
                    X(-v,k) = -1;
                end
            end
            k=k+1;
        end

    end
    fclose(fid);

    [sat,sol] = SATSolver2(X, varargin{:});
end
