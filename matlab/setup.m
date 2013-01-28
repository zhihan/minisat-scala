clear java;
addpath(pwd);
[~,name] = system('hostname');

switch deblank(name)
    % Add scala and antlr runtime to the java classpath
    case 'ah-zhan' % My Windows PC at work
        javaaddpath('C:\scala-2.9.2\lib\scala-library.jar');
    case 'zhan-deb6-64' % My linux PC at work
        javaaddpath(fullfile('/local-ssd/zhan/scala-2.9.2', ...
            'lib','scala-library.jar'));
    case 'Bo-Songs-MacBook-Pro.local'
        javaaddpath(fullfile('/Users/zhihan/scala-2.9.2/lib/scala-library.jar'));

    otherwise
        error('Don''t know what to do yet')
end

javaaddpath(fullfile(pwd, 'scala-minisat_2.9.2-0.1.jar'));
