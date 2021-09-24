#######################################################################################
#
# Xiao Song: 09/15/2021
# R code to implement the naive, RC and CR methods for rank-based estimating equations
#   with multiple covariates measured with error
#
#######################################################################################


# Suppose the maximum number of replicates (observation times) is nrep
# Each error contaminated covariates have nrep columns for the replicated measures
# Measurement error of the observations at the same sample/time may be correlated

# q is the total number of error-prone covariates
# The columns for the observations of the replicated measure for the kth covariates
# are named as Wk.1, Wk.2,...,Wk.nrep, where Wk.j is the measurement at the jth time
# The columns for the observations of the rth error-free covariates are named as 
# named as X.(q+r)

#rm(list=ls())
data.file.name <- "example_dat.txt"

isErrorCorrelated <- TRUE
isBalanced <- FALSE

n.cov.e <- 2          # number of error-prone covariates
n.cov.n <- 1          # number of error-free covariates
nrep <- 2             # number of observation times for error-prone covariates

###############################################################################
library(survival)
library(Rfast)
library(nimble)
library(evd)
library(EnvStats)
library(MGLM)
library(xtable)


if(isErrorCorrelated)
{
  n.parm.e <- n.cov.e*(n.cov.e+1)/2
}else
{
  n.parm.e <- n.cov.e
}

n.cov <- n.cov.e+n.cov.n

# error covariance matrix
if(isErrorCorrelated)
{
  error.var <- matrix(NA,n.cov.e,n.cov.e)
}else{
  error.var <- rep(NA,n.cov.e)
}

n.method <- 3
nm.ideal <- 0
nm.naive <- 1
nm.RC <- 2
nm.CorrScore <- 3
  
method.name <- c(
  "naive.smooth",
  "RC",
  "CorrScore")

out.col <- c(5,7,9,11)


GetHaz <- function(beta,X)
{
  ret <- colSums(beta*X)
}

GetVarName.X <- function(n.cov,n.cov.e,nrep,method)
{
  if(method %in% c("ideal",
                   "ideal.smooth"
                   ))
  {
    if(n.cov==1)
    {
      X.name <- "X"
    }
    else
    {
      X.name <- paste("X.",as.character(1:n.cov),sep="")
    }
  }
  else
  {
    X.name <- paste("W.bar.",as.character(1:n.cov.e),sep="")
    if(n.cov>n.cov.e)
    {
      X.name <- c(X.name,
                  paste("X.",as.character(n.cov.e+(1:(n.cov-n.cov.e))),sep="")
      )
    }
  }
  return(X.name)
}

# Compute the factor of W in E(X|W) for data
GetE.X.W <- function(isBalanced,dat,sigma2,n.cov.e,n.cov,n.parm.e,nrep)
{
  if(isBalanced)
  {
    GetE.X.W.balance(dat,sigma2,n.cov.e,n.cov,n.parm.e,nrep) 
  }
  else
  {
    GetE.X.W.unbalance(dat,sigma2,n.cov.e,n.cov,n.parm.e,nrep) 
  }
}


# Compute the factor of W in E(X|W) for data 
# with EQUAL number of replicates for subject
#
# sigma2: The estimated error covariates matrix when the errors
#         are dependent or the vector of error variances when the
#         errors are independent.
# n.cov.e: #number of error contaminated covariates
# n.cov: # of covariates
# nrep: maximum number of replicates
GetE.X.W.balance <- function(dat,sigma2,n.cov.e,n.cov,n.parm.e,nrep)
{
  X.name <- GetVarName.X(n.cov,n.cov.e,nrep,"RC")
  
  X <- dat[X.name]
  n <- nrow(dat)
  # no need for mu.X as it is canceled in the difference of E(X_i|W_i)-E(X_j|W_j)
  # E(X_i|W_i)-E(X_j|W_j)=var.X/var.W*(W_i-W_j)
  # 
  n.parm.var <- n.cov*(n.cov+1)/2
  scale.der <- array(0,c(n.cov.e,n.cov,n.parm.var))
  scale.der.e <- array(0,c(n.cov.e,n.cov,n.parm.e))
  
  if(!isErrorCorrelated && n.cov.e>1)
  {
    sigma2.temp <- diag(sigma2)/nrep
  }else
  {
    sigma2.temp <- sigma2/nrep
  }
  if(n.cov==1)
  {
    var.W <- apply(X,2,var)[1:n.cov.e]
    var.X <- var.W-sigma2.temp
    scale <- var.X/var.W
    scale.der[1,1,1] <- sigma2.temp/var.W^2
    scale.der.e[1,1,1] <- 1/(nrep*var.W^2)
    
  }else
  {
    cov.all <- cov(X)
    sigma.WW <- cov.all[1:n.cov.e,1:n.cov.e]
    sigma.XX <- sigma.WW-sigma2.temp
    if(n.cov>n.cov.e)
    {
      sigma.ZZ <- cov.all[(n.cov.e+1):n.cov,(n.cov.e+1):n.cov]
      sigma.WZ <- cov.all[1:n.cov.e,(n.cov.e+1):n.cov]
      sigma.XX.WZ <- cbind(sigma.XX,sigma.WZ)
    }else
    {
      sigma.XX.WZ <- sigma.XX
    }
    
    
    cov.all.inv <- solve(cov.all)
    scale <- sigma.XX.WZ%*%cov.all.inv
    
    
    # derivative of scalar w.r.t. each component of W and sigma2.temp
    
    scale.der <- array(0,c(n.cov.e,n.cov,n.parm.var))
    scale.der.e <- array(0,c(n.cov.e,n.cov,n.parm.e))
    
    index <- 1
    index.e <- 1
    for(i in 1:n.cov)
    {
      for(j in i:n.cov)
      {
        # derivative of cov.all w.r.t. cov.all[index]
        cov.all.der <- matrix(0,n.cov,n.cov)
        cov.all.der[i,j] <- 1
        cov.all.der[j,i] <- 1
        # derivative of (cov.all.inv) w.r.t. cov.all[index]
        cov.all.inv.der <- -cov.all.inv%*%cov.all.der%*%cov.all.inv
        # derivative of scale w.r.t. cov.all[index]
        sigma.XX.WZ.der <- matrix(0,n.cov.e,n.cov)
        
        if(i<=n.cov.e)
        {
          sigma.XX.WZ.der[i,j] <- 1
          if(j<=n.cov.e)
          {
            sigma.XX.WZ.der[j,i] <- 1
          }
          scale.der[,,index] <- sigma.XX.WZ.der%*%cov.all.inv
          if(isErrorCorrelated && n.cov.e>1 && j<=n.cov.e || i==j)
          {
            scale.der.e[,,index.e] <- -scale.der[,,index]/nrep
            index.e <- index.e+1
          }
        }
        scale.der[,,index] <- scale.der[,,index]+sigma.XX.WZ%*%cov.all.inv.der
        index <- index+1
      }
    }
  }
  
  return(list(scale=scale,scale.der=scale.der,scale.der.e=scale.der.e))
}

# Compute the factor of W in E(X|W) for data 
# with UNEQUAL number of replicates for subject
#
# sigma2: The estimated error covariates matrix when the errors
#         are dependent or the vector of error variances when the
#         errors are independent.
# n.cov.e: #number of error contaminated covariates
# n.cov: # of covariates
# nrep: maximum number of replicates
GetE.X.W.unbalance <- function(dat,sigma2,n.cov.e,n.cov,n.parm.e,nrep)
{
  X.name <- GetVarName.X(n.cov,n.cov.e,nrep,"RC")
  n.obs.name <- paste("n.obs.",as.character(1:n.parm.e),sep="")
  
  X <- dat[X.name]
  n <- nrow(dat)
  n.obs <- dat[n.obs.name]
  #  mu.X isn't canceled in the difference of E(X_i|W_i)-E(X_j|W_j) when var(W.bar)
  # is different for different subject (unequal observations)
  # E(X_i|W_i)-E(X_j|W_j)=var.X/var.W*(W_i-m-W_j)
  # 
  n.parm.var <- n.cov*(n.cov+1)/2
  
  
  mu.XZ <- apply(X,2,mean,na.rm=TRUE)
  
  cov.all <- cov(X) 
  sigma.WW.temp <-  cov.all[1:n.cov.e,1:n.cov.e]
  if(n.cov.e==1)
  {
    n.obs.inv.sum <- apply(1/n.obs,2,sum)
    sigma.XX <- sigma.WW.temp-sigma2*n.obs.inv.sum/n
  }
  else if(!isErrorCorrelated)
  {
    n.obs.inv.sum <- apply(1/n.obs,2,sum)
    sigma.XX <- sigma.WW.temp-diag(sigma2*n.obs.inv.sum/n)
  }
  else
  {
    n.obs.temp <- matrix(0,n,n.cov.e)
    for(k in 1:n.cov.e)
    {
      n.obs.temp[,k] <- n.obs[,k*(k+1)/2]
    }
    
    n.obs.inv.sum <- matrix(0,n.cov.e,n.cov.e) # sum(m[i,k,s]/(m[i,k]*m[i,s]))
    j <- 1
    for(k in 1:n.cov.e)
    {
      for(s in k:n.cov.e)
      {
        if(s>k)
        {
          n.obs.inv.sum[k,s] <- sum(n.obs[,j]/(n.obs.temp[,k]*n.obs.temp[,s]))
        }
        else
        {
          n.obs.inv.sum[k,s] <- sum(1/n.obs[,j])
        }
        j <- j+1
      }
    }
    
    n.obs.inv.sum <- lower_tri.assign(n.obs.inv.sum, upper_tri(n.obs.inv.sum))
    
    sigma.XX <- sigma.WW.temp-sigma2*n.obs.inv.sum/n
  }
  
  
  if(n.cov>n.cov.e)
  {
    
    sigma.ZZ <- cov.all[(n.cov.e+1):n.cov,(n.cov.e+1):n.cov]  #var(Z)
    sigma.WZ <- cov.all[1:n.cov.e,(n.cov.e+1):n.cov] #cov(W.bar,Z)
  }
  
  
  # scale=var.X/var.W: the factor of W in E(X|W) = mu.X+var.X/var.W(W-mu.X)
  scale <- array(0,c(n,n.cov.e,n.cov))
  scale.der <- array(0,c(n,n.cov.e,n.cov,n.parm.var)) # derivative of scale w.r.t. each component of W, except that var(W) is replaced by var(X)
  scale.der.e <- array(0,c(n,n.cov.e,n.cov,n.parm.e)) # derivative of scale w.r.t. each component of sigma2
  
  for(r in 1:n)
  {
    
    if(!isErrorCorrelated && n.cov.e>1)
    {
      sigma2.temp <- diag(sigma2/n.obs[r,])
    }else
    {
      nobs.r <- matrix(NA,n.cov.e,n.cov.e)
      nobs.r <- lower_tri.assign(nobs.r,unlist(n.obs[r,]),diag=TRUE)
      nobs.r <- upper_tri.assign(nobs.r,upper_tri(t(nobs.r),diag=FALSE))
      sigma2.temp <- sigma2/nobs.r
    }
    
    
    if(n.cov==1)
    {
      sigma.WW <- sigma.XX+sigma2.temp
      scale[r,1,1] <- sigma.XX/(sigma.WW)  # var(X)/var(W)=1-var(e)/var(W)
      scale.der[r,1,1,1] <- sigma2.temp/sigma.WW^2
      scale.der.e[r,1,1,1] <- 1/(nobs.r*sigma.WW^2)
      
    }
    else
    {
      sigma.WW <- sigma.XX+sigma2.temp
      cov.all[1:n.cov.e,1:n.cov.e] <- sigma.WW
      cov.all.inv <- solve(cov.all)
      if(n.cov>n.cov.e)
      {
        sigma.XX.WZ <- cbind(sigma.XX,sigma.WZ)
      }
      else
      {
        sigma.XX.WZ <- sigma.XX
      }
      scale[r,,] <- sigma.XX.WZ%*%cov.all.inv
    }
  }
  
  return(list(scale=scale,mu.XZ=mu.XZ))
}


# Compute the estimate of sigma.XX
# and the average of sigma2 (the error covariance matrix)
# with UNEQUAL number of replicates for subject
#
# sigma2: The estimated error covariates matrix. 
# n.cov.e: #number of error contaminated covariates
# n.cov: # of covariates
# nrep: maximum number of replicates for unbalanced data
# or number of replicates for balanced data

GetSigmaX.Sigma2.ave <- function(dat,sigma2,n.cov.e,n.cov,nrep)
{
  X.name <- GetVarName.X(n.cov,n.cov.e,nrep,"RC")
  n.obs.name <- paste("n.obs.",as.character(1:n.parm.e),sep="")
  
  X <- dat[X.name]
  n <- nrow(dat)
  n.obs <- dat[n.obs.name]
  
  if(n.cov>1)
  {
    sigma.WW <- cov(X)
  }else
  {
    sigma.WW <- var(X)
  }
  
  sigma2.ave <- matrix(0,n.cov,n.cov)
  
  if(isBalanced)
  {
    sigma2.ave[1:n.cov.e,1:n.cov.e] <- sigma2/nrep
    sigma.XX <- sigma.WW - sigma2.ave
  }else
  {
    if(!isErrorCorrelated)
    {
      n.obs.inv.sum <- apply(1/n.obs,2,sum)
      sigma2.ave[1:n.cov.e,1:n.cov.e] <- sigma2*n.obs.inv.sum/n
      sigma.XX <- sigma.WW-sigma2.ave
    }
    else
    {
      n.obs.temp <- matrix(0,n,n.cov.e)
      for(k in 1:n.cov.e)
      {
        n.obs.temp[,k] <- n.obs[,k*(k+1)/2]
      }
      
      n.obs.inv.sum <- matrix(0,n.cov.e,n.cov.e) # sum(m[i,k,s]/(m[i,k]*m[i,s]))
      j <- 1
      for(k in 1:n.cov.e)
      {
        for(s in k:n.cov.e)
        {
          if(s>k)
          {
            n.obs.inv.sum[k,s] <- sum(n.obs[,j]/(n.obs.temp[,k]*n.obs.temp[,s]))
          }
          else
          {
            n.obs.inv.sum[k,s] <- sum(1/n.obs[,j])
          }
          j <- j+1
        }
      }
      
      n.obs.inv.sum <- lower_tri.assign(n.obs.inv.sum, upper_tri(n.obs.inv.sum))
      sigma2.ave[1:n.cov.e,1:n.cov.e] <- sigma2*n.obs.inv.sum/n
      
      sigma.XX <- sigma.WW-sigma2.ave
    }
  }
  sigma.WW <- as.matrix(sigma.WW)
  return(list(sigma.XX=sigma.XX,sigma2.ave=sigma2.ave,sigma.WW=sigma.WW))
}


#Get the vector of error variances for independent errors,
# and get the error covariance matrix for dependent errors.
GetErrorVar <- function(isErrorCorrelated,dat,n.cov.e,nrep,weight)
{
  if(isErrorCorrelated)
  {
    sigma.hat <- GetErrorVar.dep(dat,n.cov.e,nrep,weight)
  }
  else{
    sigma.hat <- GetErrorVar.ind(dat,n.cov.e,nrep,weight)
  }
  return(sigma.hat)
}

# Get the vector of error variances for independent errors.
GetErrorVar.ind <- function(dat,n.cov.e,nrep,weight)
{
  W.bar.name <- paste("W.bar.",as.character(1:n.cov.e),sep="")
  W.name <- paste("W",t(outer(as.character(1:n.cov.e),as.character(1:nrep),FUN="paste",sep=".")),sep="")
  W <- dat[W.name]
  W.bar <- dat[W.bar.name]
  sigma.hat <- rep(0,n.cov.e)
  for(k in 1:n.cov.e)
  {
    W.k <- W[,(k-1)*nrep+(1:nrep)]
    n.obs.k <- as.vector(rowSums(!is.na(W.k)))
    sigma.hat[k] <- sum(weight*(W.k-W.bar[,k])^2,na.rm=TRUE)/sum(weight*(n.obs.k-1))
  }
  sigma.hat <- c(sigma.hat)
  return(sigma.hat)
}

# Get the error covariance matrix for dependent errors.
GetErrorVar.dep <- function(dat,n.cov.e,nrep,weight)
{
  W.bar.name <- paste("W.bar.",as.character(1:n.cov.e),sep="")
  
  W.bar <- dat[W.bar.name]
  sigma.hat <- matrix(0,n.cov.e,n.cov.e)
  n.obs <- dat[paste("n.obs.",as.character(1:n.parm.e),sep="")]
  j <- 1
  for(k in 1:n.cov.e)
  {
    W.k <- dat[paste("W",as.character(k),".",as.character(1:nrep),sep="")]
    for(s in k:n.cov.e)
    {
      W.s <- dat[paste("W",as.character(s),".",as.character(1:nrep),sep="")]
      sigma.hat[k,s] <- sum(weight*(W.k-W.bar[,k])*(W.s-W.bar[,s]),na.rm=TRUE)/sum(weight*(n.obs[,j]-1))
      
      j <- j+1
    }
  }
  sigma.hat <- lower_tri.assign(sigma.hat, upper_tri(sigma.hat))
  return(sigma.hat)
}

# Get the score function for error variances when errors are independent
GetErrorVar.score <- function(sigma2,dat,n.cov.e,nrep)
{
  W.bar.name <- paste("W.bar.",as.character(1:n.cov.e),sep="")
  W <- dat[paste("W",t(outer(as.character(1:n.cov.e),as.character(1:nrep),FUN="paste",sep=".")),sep="")]
  W.bar <- dat[W.bar.name]
  score <- matrix(0,n,n.cov.e)
  score.der <- matrix(0,n.cov.e,n.cov.e)
  
  for(k in 1:n.cov.e)
  {
    W.k <- W[,(k-1)*nrep+(1:nrep)]
    n.obs.k <- as.vector(rowSums(!is.na(W.k)))
    score[,k] <- apply((W.k-W.bar[,k])^2,1,sum,na.rm=TRUE)-sigma2[k]*(n.obs.k-1)
    score.der[k,k] <- score.der[k]-sum((n.obs.k-1))
  }
  return(list(score=score,score.der=score.der))
}


# Get the score function for parameters in error covariance matrix
# when errors are dependent
GetErrorVar.score.dep <- function(sigma2,dat,n.cov.e,nrep)
{
  W.bar.name <- paste("W.bar.",as.character(1:n.cov.e),sep="")
  W <- dat[paste("W",t(outer(as.character(1:n.cov.e),as.character(1:nrep),FUN="paste",sep=".")),sep="")]
  W.bar <- dat[W.bar.name]
  score <- matrix(0,n,n.parm.e)
  score.der <- matrix(0,n.parm.e,n.parm.e)
  
  index <- 1
  for(k in 1:n.cov.e)
  {
    W.k <- W[,(k-1)*nrep+(1:nrep)]
    for(s in k:n.cov.e)
    {
      W.s <- W[,(s-1)*nrep+(1:nrep)]
      n.obs.ks <- as.vector(rowSums(!is.na(W.k)&!is.na(W.s)))
      score[,index] <- (apply((W.k-W.bar[,k])*(W.s-W.bar[,s]),1,sum,na.rm=TRUE)
                        -sigma2[k,s]*(n.obs.ks-1))
      score.der[index,index] <- score.der[k,index]-sum(n.obs.ks-1)
      index <- index+1
    }
  }
  return(list(score=score,score.der=score.der))
}


# Get the Score function for the rank-based estimator
GetScore <- function(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight)
{
  if(mymethod %in% c("ideal","ideal.smooth","naive.smooth"))
  {
    fit <- GetScore.NLR.Balance(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight)
    
  }
  else if(mymethod=="RC" || mymethod=="CorrScore" && !isErrorCorrelated)
  {
    if(isBalanced)
    {
      fit <- GetScore.NLR.Balance(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight)
    }
    else
    {
      fit <- GetScore.NLR(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight)
    }
  }
  
  else if(mymethod=="CorrScore")
  {
    if(isErrorCorrelated)
    {
      if(isBalanced)
      {
        fit <- GetScore.NLR.ErrorDep.Balance(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,weight)
      }
      else
      { 
        fit <- GetScore.NLR.ErrorDep(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,weight)
      }
    }
  }
  
  return(fit)
}


# Independent error, Equal number of replicates
GetScore.NLR.Balance <- function(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight)
{
  if(mymethod!="RC") 
  {
    X.name <- GetVarName.X(n.cov,n.cov.e,nrep,mymethod)
  }else{
    X.name <- paste("E.X.W.",as.character(1:n.cov),sep="")
  }
  X <- dat[X.name]
  n <- nrow(dat)
  
  beta0 <- beta
  r <- dat$V-beta%*%t(X)
  dat.new <- data.frame(X=X,r=as.vector(r),
                        delta=dat$delta,weight=weight)
  dat.new <- dat.new[sort.list(dat.new$r),]
  r <- dat.new$r
  X <- as.matrix(dat.new[,1:n.cov],ncol=n.cov)
  
  
  delta <- dat.new$delta
  score <- rep(0,n.cov)
  X.dif <- array(0,c(n,n,n.cov))
  for(k in 1:n.cov)
  {
    X.dif[,,k] <- outer(X[,k],X[,k],"-")
  }
  if(mymethod!="CorrScore")
  {
    if(mymethod %in% c("ideal.smooth","naive.smooth","RC"))
    {
      r.dif <- pnorm(-(outer(r,r,"-")/h))
    }
    else{
      r.dif <- outer(r,r,"<")
    }
    for(k in 1:n.cov)
    {
      score[k] <- sum(delta*X.dif[,,k]*r.dif)
    }
  }
  else
  {
    e.dif <- -outer(r,r,"-")
    r.dif <- pnorm(e.dif/h)
    r.dif.der <- dnorm(e.dif/h)/h
    r.dif.der2 <- r.dif.der*(-e.dif/h)/h
    # Note that the variance of e.dif is 2sigma2/nrep, and there is no error when i=j
    for(k in 1:n.cov)
    {
      score[k] <- sum((delta*X.dif[,,k]*r.dif))
      
      if(k<=n.cov.e)
      {
        temp.matrix <- delta*r.dif.der
        diag(temp.matrix) <- 0
        score.temp.2 <- sigma2[k]/nrep*2*beta[k]*sum(temp.matrix)
        score[k] <- score[k]-score.temp.2
      }
      
      temp.matrix <- delta*X.dif[,,k]*r.dif.der2
      diag(temp.matrix) <- 0
      sigma2.beta2 <- sum(sigma2/nrep*beta[1:n.cov.e]^2)
      
      score.temp.2 <- sigma2.beta2*sum(temp.matrix)
      score[k] <- score[k]-score.temp.2
      
    }
  }
  
  return(score/n)
}

# Independent error, Unequal number of replicates
GetScore.NLR <- function(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight)
{
  if(mymethod!="RC") 
  {
    X.name <- GetVarName.X(n.cov,n.cov.e,nrep,mymethod)
  }else{
    X.name <- paste("E.X.W.",as.character(1:n.cov),sep="")
  }
  X <- dat[X.name]
  n.obs.name <- paste("n.obs.",as.character(1:n.parm.e),sep="")
  n.obs <- dat[n.obs.name]
  n <- nrow(dat)
  
  beta0 <- beta
  r <- dat$V-beta%*%t(X)
  dat.new <- data.frame(X=X,n.obs=n.obs,r=as.vector(r),
                        delta=dat$delta,weight=weight)
  dat.new <- dat.new[sort.list(dat.new$r),]
  r <- dat.new$r
  X <- as.matrix(dat.new[,1:n.cov],ncol=n.cov)
  n.obs <- as.matrix(dat.new[,n.cov+(1:n.parm.e)],ncol=n.parm.e)
  
  delta <- dat.new$delta
  score <- rep(0,n.cov)
  X.dif <- array(0,c(n,n,n.cov))
  for(k in 1:n.cov)
  {
    X.dif[,,k] <- outer(X[,k],X[,k],"-")
  }
  if(mymethod!="CorrScore")
  {
    if(mymethod %in% c("ideal.smooth","naive.smooth","RC"))
    {
      r.dif <- pnorm(-(outer(r,r,"-")/h))
    }
    else{
      r.dif <- outer(r,r,"<")
    }
    for(k in 1:n.cov)
    {
      score[k] <- sum(delta*X.dif[,,k]*r.dif)
    }
  }
  else
  {
    e.dif <- -outer(r,r,"-")
    r.dif <- pnorm(e.dif/h)
    r.dif.der <- dnorm(e.dif/h)/h
    r.dif.der2 <- r.dif.der*(-e.dif/h)/h
    
    sigma2.beta <- matrix(0,n,n.cov.e)
    beta.sigma2.beta <- rep(0,n)
    for(i in 1:n)
    {
      sigma2.i <- sigma2/n.obs[i,]
      sigma2.beta[i,] <- sigma2.i*beta[1:n.cov.e]
      beta.sigma2.beta[i] <- sum(beta[1:n.cov.e]*sigma2.beta[i,])
    }
    sigma2.beta.mat <- array(0,c(n,n,n.cov))
    for(k in 1:n.cov.e)
    {
      sigma2.beta.mat[,,k] <- outer(sigma2.beta[,k],sigma2.beta[,k],"+")
    }
    beta.sigma2.beta.mat <- outer(beta.sigma2.beta,beta.sigma2.beta,"+")
    
    # Note that the variance of e.dif is 2sigma2/nrep, and there is no error when i=j
    for(k in 1:n.cov)
    {
      score[k] <- sum((delta*X.dif[,,k]*r.dif))
      
      if(k<=n.cov.e)
      {
        temp.matrix <- delta*r.dif.der
        diag(temp.matrix) <- 0
        score.temp.2 <- sum(sigma2.beta.mat[,,k]*temp.matrix)
        score[k] <- score[k]-score.temp.2
      }
      
      temp.matrix <- delta*X.dif[,,k]*r.dif.der2
      diag(temp.matrix) <- 0
      
      score.temp.2 <- sum(beta.sigma2.beta.mat/2*temp.matrix)
      score[k] <- score[k]-score.temp.2
      
    }
  }
  
  return(score/n)
}

# Dependent error, equal number of replicates
GetScore.NLR.ErrorDep.Balance <- function(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,weight)
{
  X.name <- GetVarName.X(n.cov,n.cov.e,nrep,mymethod)
  
  X <- dat[X.name]
  beta0 <- beta
  r <- dat$V-beta%*%t(X)
  dat.new <- data.frame(X=X,r=as.vector(r),
                        delta=dat$delta,weight=weight)
  dat.new <- dat.new[sort.list(dat.new$r),]
  r <- dat.new$r
  X <- as.matrix(dat.new[,1:n.cov],ncol=n.cov)
  n <- nrow(X)
  delta <- dat.new$delta
  score <- rep(0,n.cov)
  X.dif <- array(0,c(n,n,n.cov))
  for(k in 1:n.cov)
  {
    X.dif[,,k] <- outer(X[,k],X[,k],"-")
  }
  
  e.dif <- -outer(r,r,"-")
  r.dif <- pnorm(e.dif/h)
  r.dif.der <- dnorm(e.dif/h)/h
  r.dif.der2 <- r.dif.der*(-e.dif/h)/h
  sigma2.beta <- sigma2%*%beta[1:n.cov.e]
  beta.sigma2.beta <- t(beta[1:n.cov.e])%*%sigma2.beta
  # Note that the variance of e.dif is 2sigma2/nrep, and there is no error when i=j
  for(k in 1:n.cov)
  {
    score[k] <- sum((delta*X.dif[,,k]*r.dif))
    
    if(k<=n.cov.e)
    {
      temp.matrix <- delta*r.dif.der
      diag(temp.matrix) <- 0
      score.temp.2 <- sigma2.beta[k]/nrep*2*sum(temp.matrix)
      score[k] <- score[k]-score.temp.2
    }
    
    temp.matrix <- delta*X.dif[,,k]*r.dif.der2
    diag(temp.matrix) <- 0
    score.temp.2 <- c(beta.sigma2.beta)/nrep*sum(temp.matrix)
    score[k] <- score[k]-score.temp.2
    
  }
  
  
  return(score/n)
}

# Dependent error, Unequal number of replicates
GetScore.NLR.ErrorDep <- function(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,weight)
{
  X.name <- GetVarName.X(n.cov,n.cov.e,nrep,mymethod)
  X <- dat[X.name]
  n.obs.name <- paste("n.obs.",as.character(1:n.parm.e),sep="")
  n.obs <- dat[n.obs.name]
  
  
  beta0 <- beta
  r <- dat$V-beta%*%t(X)
  dat.new <- data.frame(X=X,n.obs=n.obs,r=as.vector(r),
                        delta=dat$delta,weight=weight)
  dat.new <- dat.new[sort.list(dat.new$r),]
  r <- dat.new$r
  X <- as.matrix(dat.new[,1:n.cov],ncol=n.cov)
  n.obs <- as.matrix(dat.new[,n.cov+(1:n.parm.e)],ncol=n.parm.e)
  n <- nrow(X)
  delta <- dat.new$delta
  score <- rep(0,n.cov)
  X.dif <- array(0,c(n,n,n.cov))
  for(k in 1:n.cov)
  {
    X.dif[,,k] <- outer(X[,k],X[,k],"-")
  }
  
  e.dif <- -outer(r,r,"-")
  r.dif <- pnorm(e.dif/h)
  r.dif.der <- dnorm(e.dif/h)/h
  r.dif.der2 <- r.dif.der*(-e.dif/h)/h
  sigma2.beta <- matrix(0,n,n.cov.e)
  beta.sigma2.beta <- rep(0,n)
  for(i in 1:n)
  {
    nobs.i <- matrix(NA,n.cov.e,n.cov.e)
    nobs.i <- lower_tri.assign(nobs.i,unlist(n.obs[i,]),diag=TRUE)
    nobs.i <- upper_tri.assign(nobs.i,upper_tri(t(nobs.i),diag=FALSE))
    sigma2.i <- sigma2/nobs.i 
    sigma2.beta[i,] <- sigma2.i%*%beta[1:n.cov.e]
    beta.sigma2.beta[i] <- t(beta[1:n.cov.e])%*%sigma2.beta[i,]
  }
  sigma2.beta.mat <- array(0,c(n,n,n.cov))
  for(k in 1:n.cov.e)
  {
    sigma2.beta.mat[,,k] <- outer(sigma2.beta[,k],sigma2.beta[,k],"+")
  }
  beta.sigma2.beta.mat <- outer(beta.sigma2.beta,beta.sigma2.beta,"+")
  # Note that the variance of e.dif is 2sigma2/nrep, and there is no error when i=j
  for(k in 1:n.cov)
  {
    score[k] <- sum((delta*X.dif[,,k]*r.dif))
    
    if(k<=n.cov.e)
    {
      temp.matrix <- delta*r.dif.der
      diag(temp.matrix) <- 0
      score.temp.2 <- sum(sigma2.beta.mat[,,k]*temp.matrix)
      score[k] <- score[k]-score.temp.2
    }
    
    temp.matrix <- delta*X.dif[,,k]*r.dif.der2
    diag(temp.matrix) <- 0
    score.temp.2 <- sum(beta.sigma2.beta.mat/2*temp.matrix)
    score[k] <- score[k]-score.temp.2
    
  }
  
  return(score/n)
}

# Get Se for ideal smooth, naive method,
# and Se for RC, Corrected method with independent error, balanced data
GetSe.NLR.Balance <- function(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight)
{
  X.name <- GetVarName.X(n.cov,n.cov.e,nrep,mymethod)
  
  X <- dat[X.name]
  n <- nrow(dat)
  X.adj <- X
  
  
  if(mymethod=="RC") 
  {
     X.name <- paste("E.X.W.",as.character(1:n.cov),sep="")
     X.adj <- dat[X.name]
  }
  beta0 <- beta
  r <- dat$V-beta%*%t(X.adj)
  dat.new <- data.frame(X=X,X.adj=X.adj,r=as.vector(r),
                        delta=dat$delta,weight=weight)
  dat.new <- dat.new[sort.list(dat.new$r),]
  r <- dat.new$r
  X <- as.matrix(dat.new[,1:n.cov],ncol=n.cov)
  X.adj <- as.matrix(dat.new[,n.cov+(1:n.cov)],ncol=n.cov)
  delta <- dat.new$delta
  if(mymethod=="CorrScore" && nrep>1)
  {
    n.parm <- n.cov+n.parm.e
  }
  else
  {
    n.parm <- n.cov
  }
  score <- array(0,c(n,n,n.parm))
  score.der <- matrix(0,n.cov,n.parm)
  X.dif <- array(0,c(n,n,n.cov))
  X.dif.adj <- array(0,c(n,n,n.cov))
  for(k in 1:n.cov)
  {
    X.dif[,,k] <- outer(X[,k],X[,k],"-")
    X.dif.adj[,,k] <- X.dif[,,k]
    if(mymethod=="RC" && k<=n.cov.e)
    {
      X.dif.adj[,,k] <- outer(X.adj[,k],X.adj[,k],"-")
    }
  }
  if(mymethod!="CorrScore")
  {
    if(mymethod %in% c("ideal.smooth","naive.smooth","RC"))
    {
      e.dif <- -outer(r,r,"-")
      r.dif <- pnorm(e.dif/h)
      r.dif.der <- dnorm(e.dif/h)/h
    }
    else{
      r.dif <- outer(r,r,"<")
    }
    for(k in 1:n.cov)
    {
      temp.matrix <- delta*X.dif[,,k]*r.dif
      score[,,k] <- temp.matrix
      
      for(s in 1:n.cov)
      {
        score.der[k,s] <- sum(delta*X.dif[,,k]*r.dif.der*X.dif.adj[,,s])
      }
    }
  }
  else
  {
    e.dif <- -outer(r,r,"-")
    r.dif <- pnorm(e.dif/h)
    r.dif.der <- dnorm(e.dif/h)/h
    r.dif.der2 <- r.dif.der*(-e.dif/h)/h
    r.dif.der3 <- r.dif.der2*(-e.dif/h)/h-r.dif.der/h^2
    # Note that the variance of e.dif is 2sigma2/nrep, and there is no error when i=j
    for(k in 1:n.cov)
    {
      temp.matrix <- delta*X.dif[,,k]*r.dif
      score[,,k] <- temp.matrix                    # (1)
      
      for(s in 1:n.cov)
      {
        temp.matrix <- delta*X.dif[,,k]*r.dif.der*X.dif[,,s]
        score.der[k,s] <- score.der[k,s]+sum(temp.matrix)  # (1) factor r.dif  w.r.t. beta[s]
      }
      
      if(k<=n.cov.e)
      {
        temp.matrix <- sigma2[k]/nrep*2*beta[k]*delta*r.dif.der
        diag(temp.matrix) <- 0
        score[,,k] <- score[,,k]-temp.matrix          # (2)
        
        # (2) w.r.t. sigma2
        if(nrep>1)
        {
          score.der[k,n.cov+k] <- score.der[k,n.cov+k]-sum(temp.matrix)/sigma2[k]
        }
        
        # (2) factor of sigma2.beta w.r.t. beta[k]
        temp.matrix <- sigma2[k]/nrep*2*delta*r.dif.der
        diag(temp.matrix) <- 0
        score.der[k,k] <- score.der[k,k]-sum(temp.matrix)   # (2) factor beta[k] w.r.t. beta[k]
        
        #(2) factor of r.dif.der w.r.t beta
        for(s in 1:n.cov)
        {
          temp.matrix <- sigma2[k]/nrep*2*beta[k]*delta*r.dif.der2*X.dif[,,s]
          score.der[k,s] <- score.der[k,s]-sum(temp.matrix)   #(2) factor r.dif.der w.r.t beta[s]
        }
      }
      
      sigma2.beta2 <- sum(sigma2/nrep*beta[1:n.cov.e]^2)
      temp.matrix <- sigma2.beta2*delta*X.dif[,,k]*r.dif.der2
      score[,,k] <- score[,,k]-temp.matrix        # (3)
      
      # (3) w.r.t. sigma2
      if(nrep>1)
      {
        for(s in 1:n.cov.e)
        {
          temp.matrix <- beta[s]^2/nrep*delta*X.dif[,,k]*r.dif.der2
          score.der[k,n.cov+s] <- score.der[k,n.cov+s]-sum(temp.matrix) # (3) w.r.t. sigma2[s]
        }
      }
      
      # (3) factor of sigma2.beta2 w.r.t. beta
      for(s in 1:n.cov.e)
      {
        temp.matrix <- sigma2[s]/nrep*2*beta[s]*delta*X.dif[,,k]*r.dif.der2
        score.der[k,s] <- score.der[k,s]-sum(temp.matrix) # (3) factor of sigma2.beta2 w.r.t.  beta[s]
      }
      
      
      for(m in 1:n.cov)
      {
        temp.matrix <-  sigma2.beta2*delta*X.dif[,,k]*r.dif.der3*X.dif[,,m]
        score.der[k,m] <- score.der[k,m]-sum(temp.matrix)  # (3) factor r.dif.der2 w.r.t. beta[m]
      }
      
    }
    if(nrep>1)
    {
      fit <- GetErrorVar.score(sigma2,dat,n.cov.e,nrep)
      
      for(k in 1:n.cov.e)
      {
        score[,,n.cov+k] <- outer(fit$score[,k],fit$score[,k],"+")
        diag(score[,,n.cov+k]) <- 0
      }
      score.der.temp <- matrix(0,n.cov+n.cov.e,n.cov+n.cov.e)
      score.der.temp[1:n.cov,] <- score.der
      score.der.temp[n.cov+(1:n.cov.e),n.cov+(1:n.cov.e)] <- fit$score.der*2*(n-1)
      score.der <- score.der.temp
    }
  }
  
  score.t <- aperm(score,c(2,1,3))
  score.sym <- score+score.t
  row.sym <- apply(score.sym,c(2,3),sum)
  B.1 <- kr(row.sym,row.sym)
  B.2 <- matrix(score.sym,ncol=n.parm)
  B.2 <- kr(B.2,B.2)/2
  
  B.1 <- matrix(apply(B.1,2,sum),ncol=n.parm)
  B.2 <- matrix(apply(B.2,2,sum),ncol=n.parm)
  B <- (B.1-B.2)/(n*(n-1))^2
  A <- try(solve(score.der/(n*(n-1))),TRUE)
  V <- A%*%B%*%t(A)
  se <- sqrt(diag(V))
  
  return(se)
}

# Get Se for RC, Corrected method with 
# independent error, unequal number of replicate
GetSe.NLR <- function(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight)
{
  X.name <- GetVarName.X(n.cov,n.cov.e,nrep,mymethod)
  X <- dat[X.name]
  n.obs.name <- paste("n.obs.",as.character(1:n.parm.e),sep="")
  n.obs <- dat[n.obs.name]
  
  n <- nrow(dat)
  X.adj <- X
  
  if(mymethod=="RC") 
  {
    X.name <- paste("E.X.W.",as.character(1:n.cov),sep="")
    X.adj <- dat[X.name]
  }
  beta0 <- beta
  r <- dat$V-beta%*%t(X.adj)
  dat.new <- data.frame(X=X,X.adj=X.adj,n.obs=n.obs,r=as.vector(r),
                        delta=dat$delta,weight=weight)
  dat.new <- dat.new[sort.list(dat.new$r),]
  r <- dat.new$r
  X <- as.matrix(dat.new[,1:n.cov],ncol=n.cov)
  X.adj <- as.matrix(dat.new[,n.cov+(1:n.cov)],ncol=n.cov)
  n.obs <- as.matrix(dat.new[,2*n.cov+(1:n.cov.e)],ncol=n.cov.e)
  delta <- dat.new$delta
  if(mymethod=="CorrScore" && nrep>1)
  {
    n.parm <- n.cov+n.parm.e
  }
  else
  {
    n.parm <- n.cov
  }
  score <- array(0,c(n,n,n.parm))
  score.der <- matrix(0,n.cov,n.parm)
  X.dif <- array(0,c(n,n,n.cov))
  X.dif.adj <- array(0,c(n,n,n.cov))
  for(k in 1:n.cov)
  {
    X.dif[,,k] <- outer(X[,k],X[,k],"-")
    X.dif.adj[,,k] <- X.dif[,,k]
    if(mymethod=="RC" && k<=n.cov.e)
    {
      X.dif.adj[,,k] <- outer(X.adj[,k],X.adj[,k],"-")
    }
  }
  if(mymethod!="CorrScore")
  {
    if(mymethod %in% c("ideal.smooth","naive.smooth","RC"))
    {
      e.dif <- -outer(r,r,"-")
      r.dif <- pnorm(e.dif/h)
      r.dif.der <- dnorm(e.dif/h)/h
    }
    else{
      r.dif <- outer(r,r,"<")
    }
    for(k in 1:n.cov)
    {
      temp.matrix <- delta*X.dif[,,k]*r.dif
      score[,,k] <- temp.matrix
      
      for(s in 1:n.cov)
      {
        score.der[k,s] <- sum(delta*X.dif[,,k]*r.dif.der*X.dif.adj[,,s])
      }
    }
  }
  else
  {
    e.dif <- -outer(r,r,"-")
    r.dif <- pnorm(e.dif/h)
    r.dif.der <- dnorm(e.dif/h)/h
    r.dif.der2 <- r.dif.der*(-e.dif/h)/h
    r.dif.der3 <- r.dif.der2*(-e.dif/h)/h-r.dif.der/h^2
    
    sigma2.beta <- matrix(0,n,n.cov.e)
    beta.sigma2.beta <- rep(0,n)
    nobs.inv.i <- matrix(0,n,n.cov.e)
    for(i in 1:n)
    {
      sigma2.i <- sigma2/n.obs[i,] 
      sigma2.beta[i,] <- sigma2.i*beta[1:n.cov.e]
      nobs.inv.i[i,] <- 1/c(n.obs[i,])
    }
    nobs.inv.mat <- array(0,c(n,n,n.cov.e))
    for(k in 1:n.cov.e)
    {
      nobs.inv.mat[,,k] <- outer(nobs.inv.i[,k],nobs.inv.i[,k],"+")
    }
    
    
    # Note that the variance of e.dif is 2sigma2/nrep, and there is no error when i=j
    for(k in 1:n.cov)
    {
      temp.matrix <- delta*X.dif[,,k]*r.dif
      score[,,k] <- temp.matrix                    # (1)
      
      for(s in 1:n.cov)
      {
        temp.matrix <- delta*X.dif[,,k]*r.dif.der*X.dif[,,s]
        score.der[k,s] <- score.der[k,s]+sum(temp.matrix)  # (1) factor r.dif  w.r.t. beta[s]
      }
      
      if(k<=n.cov.e)
      {
        temp.matrix <- sigma2[k]*beta[k]*delta*nobs.inv.mat[,,k]*r.dif.der
        diag(temp.matrix) <- 0
        score[,,k] <- score[,,k]-temp.matrix          # (2)
        
        # (2) w.r.t. sigma2
        if(nrep>1)
        {
          score.der[k,n.cov+k] <- score.der[k,n.cov+k]-sum(temp.matrix)/sigma2[k]
        }
        
        # (2) factor of sigma2.beta w.r.t. beta[k]
        temp.matrix <- sigma2[k]*delta*nobs.inv.mat[,,k]*r.dif.der
        diag(temp.matrix) <- 0
        score.der[k,k] <- score.der[k,k]-sum(temp.matrix)   # (2) factor beta[k] w.r.t. beta[k]
        
        #(2) factor of r.dif.der w.r.t beta
        for(s in 1:n.cov)
        {
          temp.matrix <- sigma2[k]*beta[k]*delta*nobs.inv.mat[,,k]*r.dif.der2*X.dif[,,s]
          score.der[k,s] <- score.der[k,s]-sum(temp.matrix)   #(2) factor r.dif.der w.r.t beta[s]
        }
      }
      
      
      
      sigma2.beta2 <- apply(sigma2/n.obs*beta[1:n.cov.e]^2,1,sum)
      temp.matrix <- sigma2.beta2*delta*X.dif[,,k]*r.dif.der2
      score[,,k] <- score[,,k]-temp.matrix        # (3)
      
      # (3) w.r.t. sigma2
      if(nrep>1)
      {
        for(s in 1:n.cov.e)
        {
          temp.matrix <- beta[s]^2/n.obs[,s]*delta*X.dif[,,k]*r.dif.der2
          score.der[k,n.cov+s] <- score.der[k,n.cov+s]-sum(temp.matrix) # (3) w.r.t. sigma2[s]
        }
      }
      
      # (3) factor of sigma2.beta2 w.r.t. beta
      for(s in 1:n.cov.e)
      {
        temp.matrix <- sigma2[s]/n.obs[,s]*2*beta[s]*delta*X.dif[,,k]*r.dif.der2
        score.der[k,s] <- score.der[k,s]-sum(temp.matrix) # (3) factor of sigma2.beta2 w.r.t.  beta[s]
      }
      
      
      for(m in 1:n.cov)
      {
        temp.matrix <-  sigma2.beta2*delta*X.dif[,,k]*r.dif.der3*X.dif[,,m]
        score.der[k,m] <- score.der[k,m]-sum(temp.matrix)  # (3) factor r.dif.der2 w.r.t. beta[m]
      }
      
    }
    if(nrep>1)
    {
      fit <- GetErrorVar.score(sigma2,dat,n.cov.e,nrep)
      
      for(k in 1:n.cov.e)
      {
        score[,,n.cov+k] <- outer(fit$score[,k],fit$score[,k],"+")
        diag(score[,,n.cov+k]) <- 0
      }
      score.der.temp <- matrix(0,n.cov+n.cov.e,n.cov+n.cov.e)
      score.der.temp[1:n.cov,] <- score.der
      score.der.temp[n.cov+(1:n.cov.e),n.cov+(1:n.cov.e)] <- fit$score.der*2*(n-1)
      score.der <- score.der.temp
    }
  }
  
  score.t <- aperm(score,c(2,1,3))
  score.sym <- score+score.t
  row.sym <- apply(score.sym,c(2,3),sum)
  B.1 <- kr(row.sym,row.sym)
  B.2 <- matrix(score.sym,ncol=n.parm)
  B.2 <- kr(B.2,B.2)/2
  
  B.1 <- matrix(apply(B.1,2,sum),ncol=n.parm)
  B.2 <- matrix(apply(B.2,2,sum),ncol=n.parm)
  B <- (B.1-B.2)/(n*(n-1))^2
  A <- try(solve(score.der/(n*(n-1))),TRUE)
  V <- A%*%B%*%t(A)
  se <- sqrt(diag(V))
  
  return(se)
}

# Get Se Corrected method with 
# dependent error, equal number of replicate
GetSe.NLR.DepError.Balance <- function(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,weight)
{
  X.name <- GetVarName.X(n.cov,n.cov.e,nrep,mymethod)
  
  X <- dat[X.name]
  beta0 <- beta
  r <- dat$V-beta%*%t(X)
  dat.new <- data.frame(X=X,r=as.vector(r),
                        delta=dat$delta,weight=weight)
  dat.new <- dat.new[sort.list(dat.new$r),]
  r <- dat.new$r
  X <- as.matrix(dat.new[,1:n.cov],ncol=n.cov)
  n <- nrow(X)
  delta <- dat.new$delta
  if(mymethod!="CorrScore" || nrep==1)
  {
    n.parm <- n.cov
  }
  else{
    n.parm <- n.cov+n.parm.e
  }
  score <- array(0,c(n,n,n.parm))
  score.der <- matrix(0,n.cov,n.parm)
  X.dif <- array(0,c(n,n,n.cov))
  for(k in 1:n.cov)
  {
    X.dif[,,k] <- outer(X[,k],X[,k],"-")
  }
  
  e.dif <- -outer(r,r,"-")
  r.dif <- pnorm(e.dif/h)
  r.dif.der <- dnorm(e.dif/h)/h
  r.dif.der2 <- r.dif.der*(-e.dif/h)/h
  r.dif.der3 <- r.dif.der2*(-e.dif/h)/h-r.dif.der/h^2
  sigma2.beta <- sigma2%*%beta[1:n.cov.e]
  beta.sigma2.beta <- t(beta[1:n.cov.e])%*%sigma2.beta
  #score.der.sigma <- matrix(0,n.cov.e,n.cov.e)
  # Note that the variance of e.dif is 2sigma2/nrep, and there is no error when i=j
  for(k in 1:n.cov)
  {
    if(nrep>0)
    {
      row.index <- 0    # index for the sigma2
    }
    temp.matrix <- delta*X.dif[,,k]*r.dif
    score[,,k] <- temp.matrix                    # (1)
    
    for(s in 1:n.cov)
    {
      temp.matrix <- delta*X.dif[,,k]*r.dif.der*X.dif[,,s]
      score.der[k,s] <- score.der[k,s]+sum(temp.matrix)  # (1) factor r.dif  w.r.t. beta[s]
    }
    
    if(k<=n.cov.e)
    {
      temp.matrix <- sigma2.beta[k]/nrep*2*delta*r.dif.der
      diag(temp.matrix) <- 0
      score[,,k] <- score[,,k]-temp.matrix          # (2)
      
      # (2) der of sigma2.beta[k] w.r.t. sigma
      if(nrep>1)  
      {
        col.index <- 0
        for(s in 1:n.cov.e)
        {
          if(s>=k)
          {
            m <- row.index+(s-k+1)
          }
          else
          {
            # n.cov.e+(n.cov.e-1)+...+(n.cov.e-k+2)+(k-s+1)
            m <- col.index+(k-s+1)
          }
          temp.matrix <- beta[s]/nrep*2*delta*r.dif.der
          diag(temp.matrix) <- 0
          score.der[k,n.cov+m] <- score.der[k,n.cov+m]-sum(temp.matrix)
          col.index <- col.index+(n.cov.e-s+1)
        }
        m <- m+(n.cov.e-k)
      }
      
      # (2) der of sigma2.beta[k] w.r.t. beta
      for(s in 1:n.cov.e)
      {
        temp.matrix <- sigma2[k,s]/nrep*2*delta*r.dif.der
        diag(temp.matrix) <- 0
        score.der[k,s] <- score.der[k,s]-sum(temp.matrix)  # (2) der of sigma2.beta w.r.t. beta[s] 
      }
      
      #(2) der of factor r.dif.der w.r.t beta
      for(s in 1:n.cov)
      {
        temp.matrix <- sigma2.beta[k]/nrep*2*delta*r.dif.der2*X.dif[,,s]
        score.der[k,s] <- score.der[k,s]-sum(temp.matrix)   #(2) der of factor r.dif.der w.r.t beta
      }
    }
    
    temp.matrix <- c(beta.sigma2.beta)/nrep*delta*X.dif[,,k]*r.dif.der2
    score[,,k] <- score[,,k]-temp.matrix     # (3)
    
    # (3) der of factor r.dif.der2 w.r.t. beta
    for(m in 1:n.cov)
    {
      temp.matrix <-  c(beta.sigma2.beta)/nrep*delta*X.dif[,,k]*r.dif.der3*X.dif[,,m]
      score.der[k,m] <- score.der[k,m]-sum(temp.matrix)  # (3) factor r.dif.der2 w.r.t. beta[m]
    }
    
    # (3) der of factor beta.sigma w.r.t. sigma
    if(nrep>1)
    {
      m <- 1
      for(v in 1:n.cov.e)
      {
        for(t in v:n.cov.e)
        {
          temp.matrix <- beta[v]*beta[t]/nrep*delta*X.dif[,,k]*r.dif.der2
          score.der[k,n.cov+m] <- score.der[k,n.cov+m]-sum(temp.matrix)
          m <- m+1
        }
      }
      m<-1
      for(t in 1:n.cov.e)
      {
        for(v in t:n.cov.e)
        {
          if(v>t)
          {
            temp.matrix <- beta[t]*beta[v]/nrep*delta*X.dif[,,k]*r.dif.der2
            score.der[k,n.cov+m] <- score.der[k,n.cov+m]-sum(temp.matrix)
          }
          m <- m+1
        }
      }
    }
    
    # (3) der of factor beta.sigma.beta w.r.t. beta
    for(t in 1:n.cov.e)
    {
      for(s in 1:n.cov.e)
      {
        #(3) factor beta.sigma.beta w.r.t. factor beta[s]
        temp.matrix <- beta[t]*sigma2[s,t]/nrep*delta*X.dif[,,k]*r.dif.der2
        score.der[k,s] <- score.der[k,s]-sum(temp.matrix)
        
        #(3) factor beta.sigma.beta w.r.t. factor beta[t]
        temp.matrix <- beta[s]*sigma2[s,t]/nrep*delta*X.dif[,,k]*r.dif.der2
        score.der[k,t] <- score.der[k,t]-sum(temp.matrix)  
      }
    }
    if(nrep>1)
    {
      row.index <- row.index+(n.cov.e-k+1)
    }
  }
  if(nrep>1)
  {
    fit <- GetErrorVar.score.dep(sigma2,dat,n.cov.e,nrep)
    
    for(k in 1:n.parm.e)
    {
      score[,,n.cov+k] <- outer(fit$score[,k],fit$score[,k],"+")
      diag(score[,,n.cov+k]) <- 0
    }
    score.der.temp <- matrix(0,n.cov+n.parm.e,n.cov+n.parm.e)
    score.der.temp[1:n.cov,] <- score.der
    score.der.temp[n.cov+(1:n.parm.e),n.cov+(1:n.parm.e)] <- fit$score.der*2*(n-1)
    score.der <- score.der.temp
  }
  
  score.t <- aperm(score,c(2,1,3))
  score.sym <- score+score.t
  row.sym <- apply(score.sym,c(2,3),sum)
  B.1 <- kr(row.sym,row.sym)
  B.2 <- matrix(score.sym,ncol=n.parm)
  B.2 <- kr(B.2,B.2)/2
  
  B.1 <- matrix(apply(B.1,2,sum),ncol=n.parm)
  B.2 <- matrix(apply(B.2,2,sum),ncol=n.parm)
  B <- (B.1-B.2)/(n*(n-1))^2
  A <- try(solve(score.der/(n*(n-1))),TRUE)
  V <- A%*%B%*%t(A)
  se <- sqrt(diag(V))
  
  return(se)
}

# Get Se Corrected method with 
# dependent error, unequal number of replicate
GetSe.NLR.DepError <- function(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,weight)
{
  X.name <- GetVarName.X(n.cov,n.cov.e,nrep,mymethod)
  X <- dat[X.name]
  n.obs.name <- paste("n.obs.",as.character(1:n.parm.e),sep="")
  n.obs <- dat[n.obs.name]
  
  beta0 <- beta
  r <- dat$V-beta%*%t(X)
  dat.new <- data.frame(X=X,n.obs=n.obs,r=as.vector(r),
                        delta=dat$delta,weight=weight)
  dat.new <- dat.new[sort.list(dat.new$r),]
  r <- dat.new$r
  X <- as.matrix(dat.new[,1:n.cov],ncol=n.cov)
  n.obs <- as.matrix(dat.new[,n.cov+(1:n.parm.e)],ncol=n.parm.e)
  n <- nrow(X)
  delta <- dat.new$delta
  if(mymethod!="CorrScore" || nrep==1)
  {
    n.parm <- n.cov
  }
  else{
    n.parm <- n.cov+n.parm.e
  }
  score <- array(0,c(n,n,n.parm))
  score.der <- matrix(0,n.cov,n.parm)
  X.dif <- array(0,c(n,n,n.cov))
  for(k in 1:n.cov)
  {
    X.dif[,,k] <- outer(X[,k],X[,k],"-")
  }
  
  
  e.dif <- -outer(r,r,"-")
  r.dif <- pnorm(e.dif/h)
  r.dif.der <- dnorm(e.dif/h)/h
  r.dif.der2 <- r.dif.der*(-e.dif/h)/h
  r.dif.der3 <- r.dif.der2*(-e.dif/h)/h-r.dif.der/h^2
  sigma2.beta <- matrix(0,n,n.cov.e)
  beta.sigma2.beta <- rep(0,n)
  nobs.inv.i <- matrix(0,n,n.cov.e*n.cov.e)
  for(i in 1:n)
  {
    nobs.i <- matrix(NA,n.cov.e,n.cov.e)
    nobs.i <- lower_tri.assign(nobs.i,unlist(n.obs[i,]),diag=TRUE)
    nobs.i <- upper_tri.assign(nobs.i,upper_tri(t(nobs.i),diag=FALSE))
    sigma2.i <- sigma2/nobs.i 
    sigma2.beta[i,] <- sigma2.i%*%beta[1:n.cov.e]
    nobs.inv.i[i,] <- 1/c(nobs.i)
    
    beta.sigma2.beta[i] <- t(beta[1:n.cov.e])%*%sigma2.beta[i,]
  }
  sigma2.beta.mat <- array(0,c(n,n,n.cov.e))
  nobs.inv.mat <- array(0,c(n,n,n.cov.e*n.cov.e))
  for(k in 1:n.cov.e)
  {
    sigma2.beta.mat[,,k] <- outer(sigma2.beta[,k],sigma2.beta[,k],"+")
    for(s in k:n.cov.e)
    {
      nobs.inv.mat[,,(k-1)*n.cov.e+s] <- outer(nobs.inv.i[,(k-1)*n.cov.e+s],nobs.inv.i[,(k-1)*n.cov.e+s],"+")
    }
  }
  if(n.cov.e>1)
  {
    for(k in 2:n.cov.e)
    {
      for(s in 1:(n.cov.e-1))
      {
        nobs.inv.mat[,,(k-1)*n.cov.e+s] <- nobs.inv.mat[,,(s-1)*n.cov.e+k]
      }
    }
  }
  beta.sigma2.beta.mat <- outer(beta.sigma2.beta,beta.sigma2.beta,"+")
  #score.der.sigma <- matrix(0,n.cov.e,n.cov.e)
  # Note that the variance of e.dif is 2sigma2/nrep, and there is no error when i=j
  for(k in 1:n.cov)
  {
    if(nrep>0)
    {
      row.index <- 0    # index for the sigma2
    }
    temp.matrix <- delta*X.dif[,,k]*r.dif
    score[,,k] <- temp.matrix                    # (1)
    
    for(s in 1:n.cov)
    {
      temp.matrix <- delta*X.dif[,,k]*r.dif.der*X.dif[,,s]
      score.der[k,s] <- score.der[k,s]+sum(temp.matrix)  # (1) factor r.dif  w.r.t. beta[s]
    }
    
    if(k<=n.cov.e)
    {
      temp.matrix <- delta*sigma2.beta.mat[,,k]*r.dif.der
      diag(temp.matrix) <- 0
      score[,,k] <- score[,,k]-temp.matrix          # (2)
      
      # (2) der of sigma2.beta[,,k] w.r.t. sigma
      if(nrep>1)  
      {
        col.index <- 0
        for(s in 1:n.cov.e)
        {
          if(s>=k)
          {
            m <- row.index+(s-k+1)
          }
          else
          {
            # n.cov.e+(n.cov.e-1)+...+(n.cov.e-k+2)+(k-s+1)
            m <- col.index+(k-s+1)
          }
          temp.matrix <- beta[s]*nobs.inv.mat[,,(k-1)*n.cov.e+s]*delta*r.dif.der
          diag(temp.matrix) <- 0
          score.der[k,n.cov+m] <- score.der[k,n.cov+m]-sum(temp.matrix)
          col.index <- col.index+(n.cov.e-s+1)
        }
        m <- m+(n.cov.e-k)
      }
      
      # (2) der of sigma2.beta[,,k] w.r.t. beta
      for(s in 1:n.cov.e)
      {
        temp.matrix <- sigma2[k,s]*nobs.inv.mat[,,(k-1)*n.cov.e+s]*delta*r.dif.der
        diag(temp.matrix) <- 0
        score.der[k,s] <- score.der[k,s]-sum(temp.matrix)  # (2) der of sigma2.beta w.r.t. beta[s] 
      }
      
      
      #(2) der of factor r.dif.der w.r.t beta
      for(s in 1:n.cov)
      {
        temp.matrix <- delta*r.dif.der2*sigma2.beta.mat[,,k]*X.dif[,,s]
        score.der[k,s] <- score.der[k,s]-sum(temp.matrix)   #(2) der of factor r.dif.der w.r.t beta
      }
    }
    
    temp.matrix <- 1/2*delta*beta.sigma2.beta.mat*X.dif[,,k]*r.dif.der2
    score[,,k] <- score[,,k]-temp.matrix     # (3)
    
    # (3) der of factor r.dif.der2 w.r.t. beta
    for(m in 1:n.cov)
    {
      temp.matrix <-  1/2*delta*beta.sigma2.beta.mat*X.dif[,,k]*r.dif.der3*X.dif[,,m]
      score.der[k,m] <- score.der[k,m]-sum(temp.matrix)  # (3) factor r.dif.der2 w.r.t. beta[m]
    }
    
    # (3) der of factor beta.sigma w.r.t. sigma
    if(nrep>1)
    {
      m <- 1
      for(v in 1:n.cov.e)
      {
        for(t in v:n.cov.e)
        {
          temp.matrix <- beta[v]*beta[t]/2*nobs.inv.mat[,,(v-1)*n.cov.e+t]*delta*X.dif[,,k]*r.dif.der2
          score.der[k,n.cov+m] <- score.der[k,n.cov+m]-sum(temp.matrix)
          m <- m+1
        }
      }
      m<-1
      for(t in 1:n.cov.e)
      {
        for(v in t:n.cov.e)
        {
          if(v>t)
          {
            temp.matrix <- beta[t]*beta[v]/2*nobs.inv.mat[,,(t-1)*n.cov.e+v]*delta*X.dif[,,k]*r.dif.der2
            score.der[k,n.cov+m] <- score.der[k,n.cov+m]-sum(temp.matrix)
          }
          m <- m+1
        }
      }
    }
    
    # (3) der of factor beta.sigma.beta w.r.t. beta
    for(t in 1:n.cov.e)
    {
      for(s in 1:n.cov.e)
      {
        #(3) factor beta.sigma.beta w.r.t. factor beta[s]
        temp.matrix <- beta[t]*sigma2[s,t]/2*delta*nobs.inv.mat[,,(s-1)*n.cov.e+t]*X.dif[,,k]*r.dif.der2
        score.der[k,s] <- score.der[k,s]-sum(temp.matrix)
        
        #(3) factor beta.sigma.beta w.r.t. factor beta[t]
        temp.matrix <- beta[s]*sigma2[s,t]/2*delta*nobs.inv.mat[,,(s-1)*n.cov.e+t]*X.dif[,,k]*r.dif.der2
        score.der[k,t] <- score.der[k,t]-sum(temp.matrix)  
      }
    }
    if(nrep>1)
    {
      row.index <- row.index+(n.cov.e-k+1)
    }
  }
  if(nrep>1)
  {
    fit <- GetErrorVar.score.dep(sigma2,dat,n.cov.e,nrep)
    
    for(k in 1:n.parm.e)
    {
      score[,,n.cov+k] <- outer(fit$score[,k],fit$score[,k],"+")
      diag(score[,,n.cov+k]) <- 0
    }
    score.der.temp <- matrix(0,n.cov+n.parm.e,n.cov+n.parm.e)
    score.der.temp[1:n.cov,] <- score.der
    score.der.temp[n.cov+(1:n.parm.e),n.cov+(1:n.parm.e)] <- fit$score.der*2*(n-1)
    score.der <- score.der.temp
  }
  
  score.t <- aperm(score,c(2,1,3))
  score.sym <- score+score.t
  row.sym <- apply(score.sym,c(2,3),sum)
  B.1 <- kr(row.sym,row.sym)
  B.2 <- matrix(score.sym,ncol=n.parm)
  B.2 <- kr(B.2,B.2)/2
  
  B.1 <- matrix(apply(B.1,2,sum),ncol=n.parm)
  B.2 <- matrix(apply(B.2,2,sum),ncol=n.parm)
  B <- (B.1-B.2)/(n*(n-1))^2
  A <- try(solve(score.der/(n*(n-1))),TRUE)
  V <- A%*%B%*%t(A)
  se <- sqrt(diag(V))
  
  return(se)
}

GetScore2 <- function(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight)
{
  score <- GetScore(beta,beta.0,dat,mymethod,sigma2,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight)
  score2 <- sum(score^2)
  return(score2)
}


GetEstimate <- function(beta.ini,beta.ini.se,data,
                        GetScore2,
                        method,
                        error.var,
                        n.cov,
                        n.cov.e,
                        n.parm.e,
                        GetSe.Cox=NULL,
                        h=0.1,
                        Z=1)
  
{
  bSuccess <- FALSE
  beta <- rep(NA,n.cov)
  beta.se <- rep(NA,n.cov)
  
  E.X.W <- NULL
  if(method=="RC")
  {
      E.X.W <- GetE.X.W(isBalanced,dat,error.var,n.cov.e,n.cov,n.parm.e,nrep)
  }
  
  
  if(n.cov>1)
  {
    fit <- try(optim(beta.ini,GetScore2,
                     dat=data,n.cov=n.cov,n.cov.e=n.cov.e,n.parm.e=n.parm.e,
                     beta.0=beta.ini,
                     mymethod=method,sigma2=error.var,h=h,weight=Z,E.X.W=E.X.W))
    if(fit$convergence==0)
    {
      beta <- fit$par
    }
  }
  else
  {
    interval <- c(beta.ini-20*beta.ini.se,beta.ini+20*beta.ini.se)
    fit <- try(optim(beta.ini,GetScore2,method="Brent",
                     lower=interval[1],upper=interval[2],
                     dat=data,n.cov=n.cov,n.cov.e=n.cov.e,n.parm.e=n.parm.e,beta.0=beta.ini,
                     mymethod=method,sigma2=error.var,h=h,E.X.W=E.X.W,weight=Z))
  }

  
  sigma2.se <- rep(NA,n.parm.e)
  if(fit$convergence==0)
  {
    beta <- fit$par
    
    if(method %in% c("ideal.smooth","naive.smooth","RC"))
    {
      if(isBalanced)
      {
        se <- GetSe.NLR.Balance(beta,beta,dat,method,error.var,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight=Z)
      }
      else
      {
        se <- GetSe.NLR(beta,beta,dat,method,error.var,n.cov,n.cov.e,n.parm.e,h,E.X.W,weight=Z)
      }
      beta.se <- se[1:n.cov]
    }
    else if(method=="CorrScore")
    {
      if(isErrorCorrelated)
      {
        if(isBalanced)
        {
          se <- GetSe.NLR.DepError.Balance(beta,beta,dat,method,error.var,n.cov,n.cov.e,n.parm.e,h,weight=Z)
        }else
        {
          se <- GetSe.NLR.DepError(beta,beta,dat,method,error.var,n.cov,n.cov.e,n.parm.e,h,weight=Z)
        }
      }else
      {
        if(isBalanced)
        {
          se <- GetSe.NLR.Balance(beta,beta,dat,method,error.var,n.cov,n.cov.e,n.parm.e,h,weight=Z)
        }
        else
        {
          se <- GetSe.NLR(beta,beta,dat,method,error.var,n.cov,n.cov.e,n.parm.e,h,weight=Z)
        }
      }
      beta.se <- se[1:n.cov]
      if(method=="CorrScore")
      {
        sigma2.se <- se[n.cov+(1:n.parm.e)]
      }
    }
  }
  
  return(list(beta.est=beta,beta.se=beta.se,sigma2=error.var,sigma2.se=sigma2.se))
}


# sigma2: KxK matrix
Get.h.residual <- function(beta,residual.ls,dat,sigma2,method,weight)
{
  n <- sum(dat$delta)  
  if(method!="CorrScore")
  {
    h <- n^(-0.26)*sd(residual.ls[dat$delta>0])
  }
  else{
 
    fit <- GetSigmaX.Sigma2.ave(dat,sigma2,n.cov.e,n.cov,nrep)
    sigma2.obs <- fit$sigma2.ave
    sigma.XX <- fit$sigma.XX
    sigma.WW <- fit$sigma.WW
  
    temp <- t(beta)%*%sigma.WW%*%beta/t(beta)%*%sigma.XX%*%beta 
    h <- c(temp^2*n^(-0.26)*sd(residual.ls[dat$delta>0]))
  }
  return(h)
}


################################################################################


censor.rate <- 0

dat <- read.table(data.file.name,header=TRUE)
if(sum(dat$V<=0)>0) 
{
  stop("survival time <= 0")
}

n <- nrow(dat)
W.bar <- matrix(NA, n,n.cov.e)
n.obs <- matrix(NA, n,n.parm.e)
colnames(W.bar) <- paste("W.bar.",as.character(1:n.cov.e),sep="")
colnames(n.obs) <- paste("n.obs.",as.character(1:n.parm.e),sep="")

s <- 1

for(k in 1:n.cov.e)
{
  W1.name <- paste("W",as.character(k),".",as.character(1:nrep),sep="")
  W1 <- dat[,W1.name]
  W.bar[,k] <- apply(W1,1,mean,na.rm=TRUE)
  
  if(isErrorCorrelated)
  {
    n.temp <- n.cov.e
  }else
  {
    n.temp <- k
  }
  for(j in k:n.temp)
  {
    W2.name <- paste("W",as.character(j),".",as.character(1:nrep),sep="")
    W2 <- dat[,W2.name]
    n.obs[,s] <- apply(!is.na(W1)&!is.na(W2),1,sum,na.rm=TRUE)
    
    s <- s+1
  }
}

dat <- cbind(dat,W.bar)
dat <- cbind(dat,n.obs)

dat$V <- log(dat$V)

n <- nrow(dat)
cat("n=",n)
cat("\n")


beta.all <- matrix(NA,n.cov,n.method)
se.all <- matrix(NA,n.cov,n.method)

nm <- 1
beta.ini <- rep(0,n.cov)
beta.ini.se <- rep(0,n.cov)
while(nm <= n.method)
{
  sigma2.matrix <- matrix(0,n.parm.e,n.parm.e)
  sigma2.temp <- error.var
  
  if((method.name[nm] == "CorrScore" 
      || method.name[nm] =="RC" )
     && nrep>1
  )
  {
    if(isErrorCorrelated)
    {
      sigma2.temp <- GetErrorVar.dep(dat,n.cov.e,nrep,weight=rep(1,n))
    }
    else
    {
      sigma2.temp <- as.vector(GetErrorVar(dat,n.cov.e,nrep,weight=rep(1,n)))
    }
  } 
  
  if(!isErrorCorrelated)
  {
    diag(sigma2.matrix) <- sigma2.temp
  }else
  {
    sigma2.matrix <- sigma2.temp
  }
  if(!(method.name[nm] %in% c("CorrScore")))
  {
    X.name <- GetVarName.X(n.cov,n.cov.e,nrep,method.name[nm])
    X <- dat[X.name]
    if(method.name[nm]=="RC")
    {
      E.X.W <- GetE.X.W(isBalanced,dat,sigma2.temp,n.cov.e,n.cov,n.parm.e,nrep)
      scale <- E.X.W$scale
      if(isBalanced)
      {
        if(n.cov.e==1)
        {
          X[,1:n.cov.e] <- apply(X,1,"%*%",t(scale))
        }
        else
        {
          X[,1:n.cov.e] <- t(apply(X,1,"%*%",t(scale)))
        }
      }
      else
      {
        for(i in 1:n)
        {
          X[i,1:n.cov.e] <- as.matrix(X[i,]-E.X.W$mu.XZ)%*%t(scale[i,,])
        }
      }
      names(X) <- paste("E.X.W.",as.character(1:n.cov),sep="")
      dat <- cbind(dat,X)
    }
    model <- formula(paste("V ~ ",
                           paste(X.name, collapse=" + ")))
    fit <- lm(model,data=dat,subset=(delta==1))
    beta.ini.lst <- fit$coef[-1]
    beta.ini <- beta.ini.lst
    beta.ini.se <- coef(summary(fit))[,2][-1]
    residual.ls <- dat$V-beta.ini.lst%*%t(X)
  }
  else if(method.name[nm] == "CorrScore")
  {
    beta.ini <- beta.all[,nm.naive]
  }
  
  if(method.name[nm] %in% c("ideal.smooth","naive.smooth","CorrScore","RC"))
  {
    h <- Get.h.residual(beta.ini.lst,residual.ls,dat,sigma2.matrix,method.name[nm],weight=rep(1,n))
  }
  
  fit <- GetEstimate(beta.ini,beta.ini.se,dat,
                           GetScore2,
                     error.var=sigma2.temp,
                     method=method.name[nm],
                     h=h,
                     n.cov=n.cov,n.cov.e=n.cov.e,n.parm.e=n.parm.e,
                     Z=rep(1,n))
  
  if(method.name[nm]=="CorrScore")
  {
    if(isErrorCorrelated)
    {
      sigma2.est <- upper_tri(sigma2.matrix,diag=TRUE)
    }else
    {
      sigma2.est <- diag(sigma2.matrix)
    }
  }
  
  beta.all[,nm] <- fit$beta.est
  se.all[,nm] <- fit$beta.se
  
  if(method.name[nm]=="CorrScore" )
  {
    sigma2.se <- fit$sigma2.se
  }
  nm <- nm+1
}



#####################################################
cat("\n")

out.list.2 <- NULL
cat("+++++ Estimate of beta ++++++++\n")
cat("+++++++++++++++++++++++++++++++\n")
for(k in 1:n.cov)
{
  cat("+++++ Covariate ",k," ++++++\n")
  
  out.list.1 <- cbind(beta.all[k,],se.all[k,])
  colnames(out.list.1) <- c("est","se")
  rownames(out.list.1) <- c("naive","RC","CR")
  print(out.list.1)
}

cat("\n\n++++ parameters in the error covariance matrix +++++\n")
out.list.2 <- cbind(sigma2.est,sigma2.se)
colnames(out.list.2) <- c("est","se")
print(out.list.2)


cat("\n\n")

censor.rate <- 1-sum(dat$delta)/n
cat("censoring rate: ",censor.rate, "\n\n" )


