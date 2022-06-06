%
% matrix multiplication over power representation
%
function out=scalar_matrix_multiplication_power(a,B)
Bx=size(B,1);
By=size(B,2);
for ir=1:Bx
    for ic=1:By
        B(ir,ic)=multiplication_power(a,B(ir,ic));
    end
end
out=B;
return