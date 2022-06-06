%
% generation of primitive polynomials with degree m over GF(2)
%
function out=primitive_polynomial(m)
f=ones(1,m+1);
ff=zeros(1,m+1);
iii=0;
for ii=0:2^(m-1)-1
    f(2:m)=double(flipud(dec2bin(ii,m-1)')')-48;
    %
    alpha=zeros(2^m,m);
    alpha(1,2)=1; % alpha==[0 1 0 ... 0]
    for i=2:2^m-1
        if alpha(i-1,m)==1
            alpha(i,2:m)=alpha(i-1,1:m-1);
            alpha(i,:)=bitxor(alpha(i,:),f(1:m));
        else
            alpha(i,2:m)=alpha(i-1,1:m-1);
        end
    end
    %
    alphaA=char(alpha+48);
    alphaA=bin2dec(alphaA);
    index=zeros(1,2^m);
    for i=1:2^m
        index(alphaA(i)+1)=1;
    end
    %
    if sum(index)==2^m
        iii=iii+1;
        ff(iii,:)=f;
    end
end
out=ff;
return





