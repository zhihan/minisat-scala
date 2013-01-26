function sat_dir(wd, exp)
% 

files = dir(wd);
w = what(wd);

for i=1:length(files)
    if strcmp(files(i).name, '..') || strcmp(files(i).name, '.')
        continue;
    end
    [dummy1, dummy2, ext] = fileparts(files(i).name);
    if strcmp(ext, '.cnf')
       fprintf('\n Checking %s:\t', files(i).name);
       sat = sat_cnf([w.path filesep files(i).name]);
       if sat~= logical(exp)
           error('Wrong result in file %s', files(i).name);
       else
           fprintf('Passed');
       end
    end
end
fprintf('\n');

end