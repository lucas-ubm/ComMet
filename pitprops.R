
library(elasticnet)
data(pitprops)

corv.mtx <- pitprops                 # covariance or correlation matrix

mu <- c(0.1,0.35,0.05,0.15,0.3,0.4)    #tuning parameters
ncomponent=6                  # number of principal components
nrepeat=40                   #number of repeats in order to get the globe maximum
orthogonal=FALSE             #whether the orthogonal loadings are caculated or the uncorrelated PCs are calculated



tol <- 10^(-12) # tolerance



constMin1 <- function(a, mu)
    # max  a'x such that ||x||_mu \e 1.
{
    nvar <- length(a)
    x <- rep(1,nvar)
    aa <- abs(a)
    aa.sort <- sort(aa, decreasing=T, index.return=T)
    aas <- aa.sort$x
    aas.sum <- sum(aas)
    aas.cum <- cumsum(aas)

    flag <- ( (aas[-1] <= mu*aas.cum[-nvar]/(1+(1:(nvar-1)-1)*mu)) & (mu*aas.cum[-nvar]/(1+(1:(nvar-1)-1)*mu) < aas[-nvar]) )
    if(sum(flag)>0){
        mc <- which(flag>0)[1]
    }else{
        mc <- nvar
    }
    tmp <- mu * aas.cum[mc] / (1+(mc-1)*mu)
    x <- c(aas[1:mc] - tmp, rep(0, nvar-mc))

    b <- sort(aa.sort$ix, index.return=T)
    x <- x[b$ix]

    norm= sqrt(mu*(sum(abs(x)))^2+(1-mu)*sum(x^2))
    x <- as.numeric(lapply(a,sign)) * x / norm

    return(list(x=x, norm.lambda=norm, m=mc))
}



getFirstPC.data <- function(data, mu, tol){   #data should be n*p
    nvar <- dim(data)[2]

    v <- rnorm(nvar,0,5)
    v.old <- rep(1,nvar)
    count <- 0
    while(min(t(v-v.old)%*%(v-v.old), t(v+v.old) %*% (v+v.old)) > tol){
        count <- count + 1
        if(count > 1000) break;
        v.old <- v
        a <- data %*% v
        a <- t(data) %*% a
        ret <- constMin1(a, mu)
        v <- ret$x
    }
    v=v/sqrt(t(v)%*%v)
    return(list(loading=v, count=count))
}


getFirstPC.cov <- function(corv.mtx, mu, tol){   #input covariance/correlation matrix
    nvar <- dim(corv.mtx)[2]

    v <- rnorm(nvar,0,5)
    v.old <- rep(1,nvar)
    count <- 0
    while(min(t(v-v.old)%*%(v-v.old), t(v+v.old) %*% (v+v.old)) > tol){
        count <- count + 1
        if(count > 1000) break;
        v.old <- v
        a <- corv.mtx %*% v
        ret <- constMin1(a, mu)
        v <- ret$x
    }
    v=v/sqrt(t(v)%*%v)
    return(list(loading=v, count=count))
}



pca.norm <- function(data, mus, tol, outfile){
    #data should be n*p
    nonSps1 <- rep(0, length(mus))
    expVar1 <- nonSps1
    loadings1 <- NULL  #norm
    totVar <- sum(as.numeric(apply(data^2, 1, sum)))

    for(i in 1:length(mus)){
        ptm <- proc.time()
        out1 <- getFirstPC(data, mus[i], tol)
#        print(out1$count)
        v1 <- out1$loading
        nonSps1[i] <- sum(v1!=0)
        tmp <- data %*% v1
        expVar1[i] <- sum(tmp^2) / totVar
        loadings1 <- cbind(loadings1, v1)
        proc.time()-ptm
    }
    ret <- rbind(mus, loadings1, nonSps1, expVar1)
    write.table(ret, row.names=T, quote=F, file=outfile)
    return(ret)
}


constOpt2 <- function(a, Psi, mu, tol)
    # max  a'x such that ||x||_mu \e 1 and x is orthogonal to M, where M is spanned by the columns of Psi.
    # Psi is a p*q matrix
{   Psi=as.matrix(Psi)
    ret <- constMin1(a, mu)
    x<- ret$x              # correspond to x(t) in proof of theorem 2.6
    nu <- ret$norm / 2
    m <- ret$m
    tmp <- t(Psi) %*% x
    H <- sum(tmp^2)
    alpha <- mu / (1+(m-1)*mu)

    count1 <- 0
    dim.old <- dim(Psi)[2]
    t <- rep(0, dim.old)
    while(H>tol){
        #print(c(count1, H))
        count1 <- count1+1
        if(count1 > 60){
            #print("big count1");
            #print(c(count1, H));
            break;
        }

        signx <- sign(x)
        NPsi <- matrix(rep(signx, each=dim.old), nvar, dim.old, byrow=T) * Psi   # N %*% Psi
        NNPsi <- matrix(rep(abs(signx), each=dim.old), nvar, dim.old, byrow=T) * Psi
        K <- NNPsi - alpha * (signx %*% (t(signx) %*% Psi))
        G <- t(K) %*% (Psi %*% (t(Psi) %*% x))
        E <- (1-mu) * t(K) %*% x + mu * sum(abs(x)) * (t(K) %*% signx)
        tmp <- t(signx) %*% K
        F <- (1-mu) * t(K) %*% K + mu * t(tmp) %*% tmp
        tmp <- t(Psi) %*% K
        pai <- t(tmp) %*% tmp

        deriv.1 <- (G - H * E) / nu
        deriv.2 <- (4 * H * E %*% t(E) - 2 * (E %*% t(G) + G %*% t(E)) + pai - H * F ) / (2* nu^2)
        deriv.2 <- (deriv.2 + t(deriv.2)) / 2

#        print(c(deriv.1, deriv.2, G, H, E, pai, nu))
       if(dim.old==1)
        { if((deriv.1==0))
            {return(Psi[,1])
            }
           t.inc=-deriv.1/(deriv.2+1e-3)
         }
        else
        {
          eig.hess <- (eigen(deriv.2))$values
          positive.thresh <- max(c(0, abs(eig.hess[eig.hess<1e-6])))   # value 0 is used to avoid NULL in the latter part
        #positive.thresh= positive.thresh+min(positive.thresh, 1e-3)
           positive.thresh= positive.thresh+5e-5
         # print(c("deriv.1",deriv.1))
         #  print(c("deriv.2",eig.hess))
         # print(c("H",H))
          Hess <- deriv.2 + positive.thresh * diag(dim.old)
          # print(c("Hess",(eigen(Hess))$values))
          t.inc <- - solve(Hess, deriv.1)

         }
          t.new <- as.vector(t + t.inc)

        ret <- constMin1( a + Psi %*% t.new, mu )
        x.new <- ret$x
        H.new <- sum((t(Psi) %*% x.new)^2)
        m.new <- ret$m
        alpha.new <- mu / (1+(m.new-1)*mu)
        count2=0
        while((H.new>tol)&(H.new>H+(1e-4)*t(t.inc)%*%deriv.1)){
            count2 <- count2+1
            #print(c(count2, H,t.inc))
            if(count2 > 20){
                #print("big count2.")
                #print(count2)
                break;
            }
            t.inc <- 0.3 * t.inc
            t.new <- as.vector(t + t.inc)
            ret <- constMin1( a + Psi %*% t.new, mu )
            x.new <- ret$x
            H.new <- sum((t(Psi) %*% x.new)^2)
            m.new <- ret$m
            alpha.new <- mu / (1+(m.new-1)*mu)
        }
        if(count2 > 20){
               # print("big count2.")
                #print(count2)
                break;
            }
            
        t <- t.new
        H <- H.new
        x <- x.new
        m <- m.new
        alpha <- alpha.new
    } # end of while(H>tol)
     #print(c(count1, H))
    v <- x    # mixed norm of x is 1
    return(v)
}

time <- proc.time()

loadings <- NULL
nvar <- dim(corv.mtx)[1]


#  first PC



qq=mqq=0
for(j in 1:nrepeat)
{
    out1 <- getFirstPC.cov(corv.mtx, mu[1], tol)
    loading <- out1$loading
    qq=diag(t(loading) %*% (corv.mtx %*% loading)/sum(diag(corv.mtx)))
    #print(qq)
    if(mqq<qq)
    {v=loading
     mqq=qq
 }
 print(paste("The", j, "th repeats for the first component has been finished"))      
}
PCs=as.matrix(v)


if(orthogonal)  {Psi <- PCs} else {Psi <- corv.mtx%*%PCs; Psi=Psi/sqrt(sum(Psi^2))}


for(ncomp in 2:ncomponent)
 {
  qq=cc=rep(0,nrepeat)
   mqq=0
   for(j in 1:nrepeat){
       v <- rnorm(nvar,0,10)
       v.old <- rnorm(nvar,0,5)
       count <- 0
       while(min( sum((v-v.old)^2), sum((v+v.old)^2) ) > tol){
           count <- count + 1
           if(count > 61) { break}
           v.old <- v
           a <- corv.mtx %*% v
           a <- a - Psi %*% (t(Psi) %*% a)   # get orthogonal of a
           if (sum(abs(a))==0) stop
           v <- constOpt2(a, Psi, mu[ncomp], tol)
        #   print("254 v")
        #   print(v)
        #   print((1-mu[ncomp])*sum(v^2)+mu[ncomp]*(sum(abs(v)))^2)
       }
   #print(c("count=",count));
       loading <-  v/sqrt(sum(v^2))
       qq[j]=t(loading) %*% (corv.mtx %*% loading)
       #print(c(qq[j],(max(abs((t(loading) %*% Psi))))))
       cc[j]=max(abs((t(loading) %*% Psi)))
       if((mqq<qq[j])&(max(abs((t(loading) %*% Psi)))<10*sqrt(tol)))
       {vc=loading
         mqq=qq[j]
        
        #print(c("qq",qq[j]))
    }
       print(paste("The", j, "th repeat for", ncomp, "th component has been finished"))                              #print(count)
   }

PCs=cbind(PCs,vc)


if(orthogonal) {Psi <-cbind(Psi, vc)} else  {u=corv.mtx%*%vc; uu=u-Psi%*%(t(Psi)%*%u); Psi=cbind(Psi, uu/sqrt(sum(uu^2)))}

}
proc.time()
print("------------------------------------------------------------------")
print("The coefficients of PCs are stored in the matrix named 'PCs'!!")
print("------------------------------------------------------------------")

if(orthogonal==FALSE)
{print("The matrix t(PCs)%*%covariance%*%PCs")
print(t(PCs)%*%corv.mtx%*%PCs)} else
{print("The matrix t(PCs)%*%PCs")
print(t(PCs)%*%PCs)}
print("The proportions explained by PCs:")
print(diag(t(PCs)%*%corv.mtx%*%PCs)/sum(diag(corv.mtx)))
