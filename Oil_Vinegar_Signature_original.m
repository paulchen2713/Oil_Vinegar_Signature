% 
% Multivariate cryptography ---Oil-Vinegar Signature
% 
clear;
clc;
global m n alpha alpha1;
%
starting_time = cputime;
m = 8;
o = 17;
v = 17;
%
q = 2^m;
n = v + o;
one = q - 1;
zero = q;
%
% generation of qq(x)
%
qq = primitive_polynomial(m);
qq_size = size(qq, 1); 
qq_size = floor(qq_size * rand(1) + 1);
qq = qq(qq_size, :);
%
alpha = zeros(q, m);
alpha(1, 2) = 1; % alpha^1
for i = 2 : one % i = 2 : 2^m - 1
    if alpha(i-1, m) == 1
        alpha(i, 2:m) = alpha(i-1, 1 : m-1);
        alpha(i, :) = bitxor(alpha(i, :), qq(1:m));
    else
        alpha(i, 2:m) = alpha(i-1, 1 : m-1);
    end
end
%
alphaA = char(alpha + 48);
alphaA = bin2dec(alphaA);
alpha1 = zeros(q, 1); % zeros(2^m, 1);
for i = 1 : one % i = 1 : 2^m - 1
    alpha1(alphaA(i) + 1) = i;
end
alpha1(1) = zero;
% 
% random generation of f1, f2, ..., fo
%
F = zero * ones(n, n, o);  % 34 x 34 x 17
F1 = zero * ones(1, n, o); %  1 x 34 x 17
for io = 1 : o
    AA = floor(zero * rand(v, n) + 1);
    F(1:v, :, io) = AA;
    %
    BB = floor(zero * rand(1, n) + 1);
    F1(:, :, io) = BB; % F1(1, :, io)?
end
Fc = floor(zero * rand(1, 1, o) + 1);
%
% random generation of L1, C1 and L2, C2, generation of fb1, ..., fbo
%
indexS = 0;
while indexS == 0
    %
    % random generation of L1, C1
    %
    eyee = zero * ones(o, o);
    for in = 1 : o
        eyee(in, in) = one;
    end
    %
    indexL1 = 0; % set L1 flag to 0
    while indexL1 == 0
        L1 = floor(zero * rand(o, o) + 1);
        LL1 = [L1, eyee]; %
        LL1 = reduced_row_echelon_form_power(LL1);
        L1I = LL1(:, o+1 : 2*o);
        L1_L1I = matrix_multiplication_power(L1, L1I);
        if any(any(L1_L1I - eyee)) == 0
            indexL1 = 1; % set L1 flag to 1
        end
    end
    C1 = floor(zero * rand(o, 1) + 1);
    %
    % random generation of L2, C2
    %
    eyee = zero * ones(n, n);
    for in = 1 : n
        eyee(in, in) = one;
    end
    indexL2 = 0; % L2 flag set to 0
    while indexL2 == 0
        L2 = floor(zero * rand(n, n) + 1);
        LL2 = [L2, eyee]; %
        LL2 = reduced_row_echelon_form_power(LL2);
        L2I = LL2(:, n+1 : 2*n);
        L2_L2I = matrix_multiplication_power(L2, L2I);
        if any(any(L2_L2I - eyee)) == 0
            indexL2 = 1; % set L2 flag to 1
        end
    end
    C2 = floor(zero * rand(n, 1) + 1);
    %
    % generation of fb1, fb2, ..., fbo
    %
    FBB = zero * ones(n, n, o);  % 34 x 34 x 17
    FBB1 = zero * ones(1, n, o); %  1 x 34 x 17
    FBBc = zero * ones(1, 1, o); %  1 x  1 x 17
    for io = 1 : o
        FBB(:, :, io) = matrix_multiplication_power(matrix_multiplication_power(L2', F(:, :, io)), L2);
        FBB11 = matrix_multiplication_power(matrix_multiplication_power(C2', (F(:, :, io))'), L2);
        FBB12 = matrix_multiplication_power(matrix_multiplication_power(C2', F(:, :, io)), L2);
        FBB13 = matrix_multiplication_power(F1(:, :, io), L2); % F1(1, :, io)?
        %
        FBB1(:, :, io) = matrix_addition_power(matrix_addition_power(FBB11, FBB12), FBB13); % FBB1(1, :, io)?
        FBBc1 = matrix_multiplication_power(matrix_multiplication_power(C2', F(:, :, io)), C2);
        FBBc2 = matrix_multiplication_power(F1(:, :, io), C2); % F1(1, :, io)?
        FBBc(1, 1, io) = matrix_addition_power(matrix_addition_power(FBBc1, FBBc2), Fc(1, 1, io));
    end
    %
    FB = zero * ones(n, n, o);  % 34 x 34 x 17
    FB1 = zero * ones(1, n, o); %  1 x 34 x 17
    FBc = zero * ones(1, 1, o); %  1 x  1 x 17
    for io1 = 1 : o
        for io2 = 1 : o
            LFL = scalar_matrix_multiplication_power(L1(io1, io2), FBB(:, :, io2));
            LFL1 = scalar_matrix_multiplication_power(L1(io1, io2), FBB1(:, :, io2)); % FBB1(1, :, io2))?
            LFLc = multiplication_power(L1(io1, io2), FBBc(1, 1, io2)); % 
            FB(:, :, io1) = matrix_addition_power(FB(:, :, io1), LFL);
            FB1(:, :, io1) = matrix_addition_power(FB1(:, :, io1), LFL1); % FB1(1, :, io1)?
            FBc(1, 1, io1) = addition_power(FBc(1, 1, io1), LFLc);
        end
        FBc(1, 1, io1) = addition_power(FBc(1, 1, io1), C1(io1));
    end
    %
    % public key: m, n, fb1, fb2, ..., fbo
    % private key: L1, L2, f1, f2, ..., fo
    %
    % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %
    %
    % generation of signature
    %
    % document: Y
    %
    % random generation of Vinegar
    %
    message = 'Exactly 17 Words!';
    Y = (double(message))';
    V = floor(zero * rand(v, 1) + 1);
    %
    % compute YB = L1^(-1)(y)
    %
    YB = matrix_addition_power(Y, C1);
    YB = matrix_multiplication_power(L1I, YB);
    %
    S = zero * ones(o, o);
    Sr = zero * ones(o, 1);
    for io = 1 : o
        A = F(1 : v, 1 : v, io);
        B = F(1 : v, v+1 : n, io);
        c = F1(1, 1 : v, io);
        d = F1(1, v+1 : n, io);
        S(io, :) = matrix_addition_power(matrix_multiplication_power(V', B), d);
        Sr1 = matrix_multiplication_power(matrix_multiplication_power(V', A), V);
        Sr2 = matrix_multiplication_power(c, V);
        Sr(io) = addition_power(addition_power(addition_power(Sr1, Sr2), YB(io)), Fc(1, 1, io));
    end
    %
    % SI = S^(-1)
    %
    eyee = zero * ones(o, o);
    for io1 = 1 : o
        eyee(io1, io1) = one;
    end
    SS = [S, eyee];
    SS = reduced_row_echelon_form_power(SS);
    SI = SS(:, o+1 : 2*o);
    S_SI = matrix_multiplication_power(S, SI);
    if any(any(S_SI - eyee)) == 0
        indexS = 1; % set S flag to 1
    end
end
%
X = matrix_multiplication_power(SI, Sr);
XB = [V; X];
%
% z = L2^(-1)(XB)
%
XBc = matrix_addition_power(XB, C2);
z = matrix_multiplication_power(L2I, XBc);
%
% send the message:
%   (signature-message pair) = (z, m)
%
% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %
%
% signature verification
%
check = zeros(o, 1);
for io = 1 : o
    check1 = matrix_multiplication_power(matrix_multiplication_power(z', FB(:, :, io)), z);
    check2 = matrix_multiplication_power(FB1(:, :, io), z);
    check(io) = matrix_addition_power(matrix_addition_power(check1, check2), FBc(1, 1, io));
end
%
message_R = char(check');
%
%
if any(message - message_R) == 0
    fprintf('Valid signature. \n\n');
else
    fprintf('Invalid signature. \n\n');
end
%
ending_time = cputime;
computation_time = ending_time - starting_time;
%
fprintf('the original message is: %s\n', message);
fprintf('the recovery message is: %s\n', message_R);
fprintf('the computation time is: %f sec\n', computation_time);
%
% Valid signature. 
% 
% the original message is: TokyoOlympics2021
% the recovery message is: TokyoOlympics2021
% the computation time is: 41.265625 sec
%
% Valid signature. 
% 
% the original message is: Exactly 17 Words!
% the recovery message is: Exactly 17 Words!
% the computation time is: 44.234375 sec
%

