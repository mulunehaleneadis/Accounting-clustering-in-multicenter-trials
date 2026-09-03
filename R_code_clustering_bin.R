rm(list = ls())

##Settings
#loading important libraries
library(mvtnorm)
library(dplyr)
library(lme4)
library(sandwich)
library(ggplot2)
library(tidyverse)
library(gridExtra)
library(reshape2)
library(gee)
library(stdReg)
library(drgee)
library(geepack)
library(nlme)
library(glmtoolbox)
library(metafor)
library(cowplot)
library(grid)
library(ggpubr)
library(speff2trial) 
library(readstata13)
library(LaplacesDemon)
library(xtable)
library(lme4)

invlogit <- function(x) {1/(1+exp(-x))}

#######################################################################################################
#Naive estimator without covariates
Naive_fun <- function(data,trt,y) {
  model_naive <- glm(y~trt, data = data,family=binomial(link = "logit"))
  data_0 <-  data.frame(trt=0)
  data_1 <- data.frame(trt=1)
  pred_0 <- predict(model_naive, newdata = data_0,type = "response")
  pred_1 <- predict(model_naive, newdata = data_1,type = "response")
  p <- mean(trt)
  IF0 <- (1 - trt)/(1-p)*(y-pred_0) + pred_0
  IF1 <- trt /p* (y - pred_1) + pred_1
  IF  <- IF1-IF0
  return(list(IF1,IF))
}
#####################################################################################################################

##Naive estimator with covariates
Naive_cov_fun <- function(data,trt,x1,x2,x3,x4,y) {
  model_naive_cov <- glm(y~trt+x1+x2+x3+x4, data = data,family=binomial(link = "logit"))
  data_0 <-  data.frame(trt=0,x1,x2,x3,x4)
  data_1 <- data.frame(trt=1,x1,x2,x3,x4)
  pred_0 <- as.vector(predict(model_naive_cov, newdata = data_0,type = "response"))
  pred_1 <- as.vector(predict(model_naive_cov, newdata = data_1,type = "response"))
  p_model <- glm(trt~x1+x2+x3+x4,data = data,family=binomial(link = "logit"))
  new_dta <-  data.frame(x1,x2,x3,x4)
  p<- as.vector(predict(p_model, newdata = new_dta,type = "response"))
  IF0 <- (1 - trt)/(1-p)*(y-pred_0) + pred_0
  IF1 <- trt /p* (y - pred_1) + pred_1
  IF  <- IF1 - IF0
  return(list(IF1,IF))
}
##################################################################################################################

#Fixed without covariates
fixed_fun<- function(data,c,trt,y) {
  model_fixed <- glm(y~trt+as.factor(c), data = data,family=binomial(link = "logit"))
  data_0 <-  data.frame(c,trt=0)
  data_1 <- data.frame(c,trt=1)
  pred_0 <- predict(model_fixed, newdata = data_0,type = "response")
  pred_1 <- predict(model_fixed, newdata = data_1,type = "response")
  p_model <- glmer(trt~1+(1|c),data = data,nAGQ=0,family=binomial(link = "logit"))
  new_dta<- data.frame(c)
  p <- as.numeric(predict(p_model, newdata = new_dta,type = "response"))
  IF0 <- (1 - trt)/(1-p)*(y-pred_0) + pred_0
  IF1 <- trt /p* (y - pred_1) + pred_1
  IF  <- IF1 - IF0
  return(list(IF1,IF))
}
#################################################################################################################

#Fixed with covariates
fixed_cov_fun <- function(data,c,trt,x1,x2,x3,x4,y) {
  model_fixed_cov <- glm(y~trt+x1+x2+x3+x4+as.factor(c), data = data,family=binomial(link = "logit"))
  data_0 <-  data.frame(c,trt=0,x1,x2,x3,x4)
  data_1 <- data.frame(c,trt=1,x1,x2,x3,x4)
  pred_0 <- predict(model_fixed_cov, newdata = data_0,type = "response")
  pred_1 <- predict(model_fixed_cov,newdata = data_1,type = "response")
  p_model <- glmer(trt~x1+x2+x3+x4+(1|c),data = data,nAGQ=0,family=binomial(link = "logit"))
  new_dta <-  data.frame(c,x1,x2,x3,x4)
  p<- as.vector(predict(p_model, newdata = new_dta,type = "response"))
  IF0 <- (1 - trt)/(1-p)*(y-pred_0) + pred_0
  IF1 <- trt /p* (y - pred_1) + pred_1
  IF  <- IF1 - IF0
  return(list(IF1,IF))
}
#################################################################################################################

#mixed-effects with only random intercepts and without covariates
###Estimating random effects using empirical BLUPs
mixed_fun <- function(data,c,trt,y) {
  model_mixed <- glmer(y~trt+(1|c), data = data,nAGQ=0,family=binomial(link = "logit"))
  data_0 <-  data.frame(c,trt=0)
  data_1 <- data.frame(c,trt=1)
  pred_0 <- predict(model_mixed, newdata = data_0,type = "response")
  pred_1 <- predict(model_mixed, newdata = data_1,type = "response")
  p_model <- glmer(trt~1+(1|c),data = data,nAGQ=0,family=binomial(link = "logit"))
  new_dta<- data.frame(c)
  p <- as.numeric(predict(p_model, newdata = new_dta,type = "response"))
  IF0 <- (1 - trt)/(1-p)*(y-pred_0) + pred_0
  IF1 <- trt /p* (y - pred_1) + pred_1
  IF  <- IF1 - IF0
  return(list(IF1,IF))
}
#######################################################################################################################

#mixed-effects with only random intercepts and without covariates
###Estimating random effects by drawing from normal distribution based on the estimated random effects variances
mixed_simulated_fun <- function(data,c,trt,y) {
  #model fitting
  model_mixed_simulated <- glmer(y~trt+(1|c), data = data,nAGQ=0,family=binomial(link = "logit"))
  
  #Only fixed-effects predictions 
  data_0 <- data.frame(c, trt = 0)
  data_1 <- data.frame(c, trt = 1)
  pred_fix_0 <- as.vector(predict(model_mixed_simulated, newdata = data_0,type = "link",re.form = NA))
  pred_fix_1 <- as.vector(predict(model_mixed_simulated, newdata = data_1,type = "link",re.form = NA))
  
  #random-intercept variance
  vc_df <- as.data.frame(VarCorr(model_mixed_simulated))
  intercept_var <- vc_df$vcov[1]
  
  #Storage for averages over 1000 simulations
  n <- length(trt)
  IF1_sum <- numeric(n)
  IF_sum  <- numeric(n)
  
  p_model <- glmer(trt~1+(1|c),data = data,nAGQ=0,family=binomial(link = "logit"))
  new_dta<- data.frame(c)
  p <- as.numeric(predict(p_model, newdata = new_dta,type = "response"))
  
  nsim <- 1000
  for (i in 1:nsim) {
    #Simulate random intercepts from estimated variance
    est_u0 <- rnorm(length(unique(c)), 0, sqrt(intercept_var))
    
    #Add RE, get probabilities
    pred_0 <- plogis(pred_fix_0 + est_u0[c])
    pred_1 <- plogis(pred_fix_1 + est_u0[c])
    
    #Influence functions
    IF0 <- (1 - trt)/(1 - p) * (y - pred_0) + pred_0
    IF1 <- trt /p* (y - pred_1) + pred_1
    IF  <- IF1 - IF0
    
    IF1_sum <- IF1_sum + IF1
    IF_sum  <- IF_sum  + IF
  }
  
  inf1 <- IF1_sum/nsim
  inf   <- IF_sum/nsim
  return(list(inf1, inf))
}
############################################################################################################################

#mixed-effects with only random intercepts and with covariates
###Estimating random effects using empirical BLUPs
#mixed_cov
mixed_cov_fun <- function(data,c,trt,x1,x2,x3,x4,y) {
  model_mixed_cov <- glmer(y~trt+x1+x2+x3+x4+(1|c), data = data,nAGQ=0,family=binomial(link = "logit"))
  data_0 <-  data.frame(c,trt=0,x1,x2,x3,x4)
  data_1 <- data.frame(c,trt=1,x1,x2,x3,x4)
  pred_0 <- predict(model_mixed_cov, newdata = data_0,type = "response")
  pred_1 <- predict(model_mixed_cov,newdata = data_1,type = "response")
  p_model <- glmer(trt~x1+x2+x3+x4+(1|c),data = data,nAGQ=0,family=binomial(link = "logit"))
  new_dta <-  data.frame(c,x1,x2,x3,x4)
  p<- as.vector(predict(p_model, newdata = new_dta,type = "response"))
  IF0 <- (1 - trt)/(1-p)*(y-pred_0) + pred_0
  IF1 <- trt /p* (y - pred_1) + pred_1
  IF  <- IF1 - IF0
  return(list(IF1,IF))
}
########################################################################################################################

#mixed-effects with only random intercepts and with covariates
###Estimating random effects by drawing from normal distribution based on the estimated random effects variances
mixed_cov_simulated <- function(data,c,trt,x1,x2,x3,x4,y) {
  #model fitting
  model_mixed_cov_simulated <-  glmer(y~trt+x1+x2+x3+x4+(1|c), data = data,nAGQ=0,family=binomial(link = "logit"))
  
  #Only fixed-effects predictions 
  data_0 <-  data.frame(c,trt=0,x1,x2,x3,x4)
  data_1 <- data.frame(c,trt=1,x1,x2,x3,x4)
  pred_fix_0 <- as.vector(predict(model_mixed_cov_simulated, newdata = data_0,type = "link",re.form = NA))
  pred_fix_1 <- as.vector(predict(model_mixed_cov_simulated, newdata = data_1,type = "link",re.form = NA))
  
  #random-intercept variance
  vc_df <- as.data.frame(VarCorr(model_mixed_cov_simulated))
  intercept_var <- vc_df$vcov[1]
  
  #Storage for averages over 1000 simulations
  n <- length(trt)
  IF1_sum <- numeric(n)
  IF_sum  <- numeric(n)
  
  p_model <- glmer(trt~x1+x2+x3+x4+(1|c),data = data,nAGQ=0,family=binomial(link = "logit"))
  new_dta <-  data.frame(c,x1,x2,x3,x4)
  p<- as.vector(predict(p_model, newdata = new_dta,type = "response"))
  nsim <- 1000
  
  for (i in 1:nsim) {
    #Simulate random intercepts from estimated variance
    est_u0 <- rnorm(length(unique(c)), 0, sqrt(intercept_var))
    
    #Add RE, get probabilities
    pred_0 <- plogis(pred_fix_0 + est_u0[c])
    pred_1 <- plogis(pred_fix_1 + est_u0[c])
    
    #Influence functions
    IF0 <- (1 - trt)/(1 - p)*(y-pred_0)+pred_0
    IF1 <- trt/p*(y-pred_1) + pred_1
    IF  <- IF1 - IF0
    
    IF1_sum <- IF1_sum + IF1
    IF_sum  <- IF_sum  + IF
  }
  
  inf1 <- IF1_sum/nsim
  inf   <- IF_sum/nsim
  return(list(inf1, inf))
}
####################################################################################################################

#mixed models with random intercepts and slops but without covariates
###Estimating random-effects using empirical BLUPs
mixed_slope_fun <- function(data,c,trt,y) {
  model_mixed_slope <- glmer(y~trt+(1+trt|c), data = data,nAGQ=0,family=binomial(link = "logit"))
  data_0 <-  data.frame(c,trt=0)
  data_1 <- data.frame(c,trt=1)
  pred_0 <- predict(model_mixed_slope, newdata = data_0,type = "response")
  pred_1 <- predict(model_mixed_slope, newdata = data_1,type = "response")
  p_model <- glmer(trt~1+(1|c),data = data,nAGQ=0,family=binomial(link = "logit"))
  new_dta<- data.frame(c)
  p <- as.numeric(predict(p_model, newdata = new_dta,type = "response"))
  IF0 <- (1 - trt)/(1-p)*(y-pred_0) + pred_0
  IF1 <- trt /p* (y - pred_1) + pred_1
  IF  <- IF1 - IF0
  return(list(IF1,IF))
}
####################################################################################################################

#mixed-effects with random intercepts and random slopes but without covariates
###Estimating random effects by drawing from normal distribution based on the estimated random effects variances
model_slope_fun <- function(data,c,trt,y) {
  #model fitting
  model_mixed_slope <-  glmer(y~trt+(1+trt|c), data = data,nAGQ=0,family=binomial(link = "logit"))
  
  #Only fixed-effects predictions 
  data_0 <-  data.frame(c,trt=0)
  data_1 <- data.frame(c,trt=1)
  pred_fix_0 <- as.vector(predict(model_mixed_slope, newdata = data_0,type = "link",re.form = NA))
  pred_fix_1 <- as.vector(predict(model_mixed_slope, newdata = data_1,type = "link",re.form = NA))
  
  #random-intercept variance
  vc_df <- as.data.frame(VarCorr(model_mixed_slope))
  intercept_var <- vc_df$vcov[1]
  
  #random-slope variance
  slope_var_trt <- vc_df$vcov[vc_df$var1 == "trt" & is.na(vc_df$var2)]
  
  #Storage for averages over 1000 simulations
  n <- length(trt)
  IF1_sum <- numeric(n)
  IF_sum  <- numeric(n)
  
  p_model <- glmer(trt~1+(1|c),data = data,nAGQ=0,family=binomial(link = "logit"))
  new_dta<- data.frame(c)
  p <- as.numeric(predict(p_model, newdata = new_dta,type = "response"))
  
  nsim <- 1000
  
  for (i in 1:nsim) {
    #Simulate random intercepts and slopes from estimated variances
    est_u0 <- rnorm(length(unique(c)), 0, sqrt(intercept_var))
    est_u1 <- rnorm(length(unique(c)), 0, sqrt(slope_var_trt))
    
    #Add RE, get probabilities
    pred_0 <- plogis(pred_fix_0 + est_u0[c])
    pred_1 <- plogis(pred_fix_1 + est_u0[c]+est_u1[c])
    
    #Influence functions
    IF0 <- (1 - trt)/(1 - p) * (y - pred_0) + pred_0
    IF1 <- trt /p* (y - pred_1) + pred_1
    IF  <- IF1 - IF0
    
    IF1_sum <- IF1_sum + IF1
    IF_sum  <- IF_sum  + IF
  }
  
  inf1 <- IF1_sum/nsim
  inf   <- IF_sum/nsim
  return(list(inf1, inf))
}
#################################################################################################################################

#mixed models with random intercepts and slops but with covariates
###Estimating random-effects using empirical BLUPs
mixed_cov_slope_fun <- function(data,c,trt,x1,x2,x3,x4,y) {
  model_mixed_cov_slope <- glmer(y~trt+x1+x2+x3+x4+(1+trt|c), data = data,nAGQ=0,family=binomial(link = "logit"))
  data_0 <-  data.frame(c,trt=0,x1,x2,x3,x4)
  data_1 <- data.frame(c,trt=1,x1,x2,x3,x4)
  pred_0 <- predict(model_mixed_cov_slope, newdata = data_0,type = "response")
  pred_1 <- predict(model_mixed_cov_slope,newdata = data_1,type = "response")
  p_model <- glmer(trt~x1+x2+x3+x4+(1|c),data = data,nAGQ=0,family=binomial(link = "logit"))
  new_dta <-  data.frame(c,x1,x2,x3,x4)
  p<- as.vector(predict(p_model, newdata = new_dta,type = "response"))
  IF0 <- (1 - trt)/(1-p)*(y-pred_0) + pred_0
  IF1 <- trt /p* (y - pred_1) + pred_1
  IF  <- IF1 - IF0
  return(list(IF1,IF))
}
#############################################################################################################

#mixed models with random intercepts and slops but also with covariates
#mixed-effects with random intercepts and random slopes and with covariates
mixed_cov_slope_simulated_fun <- function(data,c,trt,x1,x2,x3,x4,y) {
  #model fitting
  model_mixed_cov_slope_simulated <-  glmer(y~trt+x1+x2+x3+x4+(1+trt|c), data = data,nAGQ=0,family=binomial(link = "logit"))
  
  #Only fixed-effects predictions 
  data_0 <-  data.frame(c,trt=0,x1,x2,x3,x4)
  data_1 <- data.frame(c,trt=1,x1,x2,x3,x4)
  pred_fix_0 <- as.vector(predict(model_mixed_cov_slope_simulated, newdata = data_0,type = "link",re.form = NA))
  pred_fix_1 <- as.vector(predict(model_mixed_cov_slope_simulated, newdata = data_1,type = "link",re.form = NA))
  
  #random-intercept variance
  vc_df <- as.data.frame(VarCorr(model_mixed_cov_slope_simulated))
  intercept_var <- vc_df$vcov[1]
  
  #random-slope variance
  slope_var_trt <- vc_df$vcov[vc_df$var1 == "trt" & is.na(vc_df$var2)]
  
  #Storage for averages over 1000 simulations
  n <- length(trt)
  IF1_sum <- numeric(n)
  IF_sum  <- numeric(n)
  
  p_model <- glmer(trt~x1+x2+x3+x4+(1|c),data = data,nAGQ=0,family=binomial(link = "logit"))
  new_dta <-  data.frame(c,x1,x2,x3,x4)
  p<- as.vector(predict(p_model, newdata = new_dta,type = "response"))
  
  nsim <- 1000
  
  for (i in 1:nsim) {
    #Simulate random intercepts and slopes from estimated variances
    est_u0 <- rnorm(length(unique(c)), 0, sqrt(intercept_var))
    est_u1 <- rnorm(length(unique(c)), 0, sqrt(slope_var_trt))
    
    #Add RE, get probabilities
    pred_0 <- plogis(pred_fix_0 + est_u0[c])
    pred_1 <- plogis(pred_fix_1 + est_u0[c]+est_u1[c])
    
    #Influence functions
    IF0 <- (1 - trt)/(1 - p)*(y - pred_0) + pred_0
    IF1 <- trt /p* (y - pred_1)+pred_1
    IF  <- IF1 - IF0
    
    IF1_sum <- IF1_sum + IF1
    IF_sum  <- IF_sum  + IF
  }
  
  inf1 <- IF1_sum/nsim
  inf   <- IF_sum/nsim
  return(list(inf1, inf))
}
############################################################################################################

calc_me_var <- function(data,c,inf,nc) {
  means_1 <- as.vector(tapply(inf[[1]], c, mean))
  mixed_1 <-lmer(inf[[1]]~(1|c),data = data)
  res_var_1 <- sigma(mixed_1)^2/nc
  means <- as.vector(tapply(inf[[2]], c, mean))
  mixed <-lmer(inf[[2]]~(1|c),data = data)
  res_var <- sigma(mixed)^2/nc
  return(list(means_1,res_var_1,means,res_var,nc))
}

#function to calculate the variance of random effects from meta-analysis
tau_square <- function(means, variances) {
  model_REML <- rma(yi = means, vi = variances, method = "REML",
                    control = list(stepadj = 0.5, maxiter = 10000))
  tau2_REML <- model_REML$tau2
  model_DL <- rma(yi = means, vi = variances, method = "DL")
  tau2_DL <- model_DL$tau2
  m <- length(means)  
  var_means <- mean((means - mean(means))^2)
  sum_variances <- sum(variances)
  v <- var_means-((m - 1)/m^2)*sum_variances
  tau2_AD <- max(0,v)
  return(list(tau2_REML,tau2_DL,tau2_AD))
}
#######################################################################################################

#approximate degree of freedom
cal_t <- function(tau2, res_variance, nc) {
  tau2 <- max(0, tau2)
  rho <- tau2/(tau2 + res_variance)
  df <- sum(nc/(1 + (nc - 1) * rho)) - 1
  t_critical <- -qt(0.025, df)
  return(t_critical)
}
##########################################################################################################

####>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
#Simulated MISTIE_III trial data
data_url <-
  paste0("https://github.com/jbetz-jhu/CovariateAdjustmentTutorial",
         "/raw/main/Simulated_MISTIE_III_v1.2.csv")
#Read in data: Recast categorical variables as factors
data <- read.csv(file = url(data_url))
#Re-coding of variables
data$ich_location <- ifelse(data$ich_location == "Deep", 1, 0)
data$arm <- ifelse(data$arm == "surgical", 1, 0)
recode_gcs <- function(x) {
  factor_levels <- c("1. Severe (3-8)" = 2, "2. Moderate (9-12)" = 1, "3. Mild (13-15)" = 0)
  return(factor_levels[x])
}
data$gcs_category_numeric <- sapply(data$gcs_category, recode_gcs)
#Create dummy variables for GCS
data$gcs_sever <- ifelse(data$gcs_category_numeric == 2, 1, 0)
data$gcs_moderate <- ifelse(data$gcs_category_numeric == 1, 1, 0)
recode_out <- function(x) {
  factor_levels <- c("0-1" = 1,"2" = 1, "3" = 1,"4" = 0, "5" = 0, "6" = 0)
  return(factor_levels[x])
}
data$outcome <- sapply(data$mrs_365d_complete, recode_out)
data <- na.omit(data)
data_to_sample <- data[, c("gcs_sever","gcs_moderate","age","ich_s_volume")]

###>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
Simulation_function <- function(k,nc,sigma_sequare_u0,sigma_sequare_u1,sigma_sequare_u2){
  n <- sum(nc)
  sampled_dta <- data_to_sample[sample(1:nrow(data_to_sample), size = n, replace = TRUE),]
  x1 <- sampled_dta$gcs_sever
  x2 <- sampled_dta$gcs_moderate
  x3 <- sampled_dta$age
  x4 <- sampled_dta$ich_s_volume
  trt <- rbinom(n,1,0.5)
  c <- rep(1:k,nc)
  u0 <- rnorm(k, 0, sqrt(sigma_sequare_u0))
  u1 <- rnorm(k, 0, sqrt(sigma_sequare_u1))
  u2 <- rnorm(k, 0, sqrt(sigma_sequare_u2))
  y <- rbinom(n,1,invlogit(3.22+u0[c]+(0.28+u1[c])*trt-(1.71+u2[c])*x1-0.72*x2-0.04*x3-0.007*x4))
  #The true counterfactual mean is determined from a very large Monte Carlo simulation
  dta <- data.frame(c,trt,x1,x2,x3,x4,y)
  
  ################################################################################################################################################
  # ========= Naive estimator without covariates =========
  #unadjusted
  model_naive <- Naive_fun(dta,trt,y)
  coef_naive_1 <- mean(model_naive[[1]])
  coef_naive <- mean(model_naive[[2]])
  se_naive_1 <- sqrt(var(model_naive[[1]])/n)
  se_naive <- sqrt(var(model_naive[[2]])/n)
  rho <- 0
  df_naive <- sum(nc/(1+(nc-1)*rho))-1
  t_naive <- -qt(0.025,df_naive)
  
  ################################################################################################################################################
  # ========= Naive estimator with covariates =========
  #unadjusted_cov
  model_naive_cov <- Naive_cov_fun(dta,trt,x1,x2,x3,x4,y)
  coef_naive_1_cov <- mean(model_naive_cov[[1]])
  coef_naive_cov <- mean(model_naive_cov[[2]])
  se_naive_1_cov <- sqrt(var(model_naive_cov[[1]])/n)
  se_naive_cov <- sqrt(var(model_naive_cov[[2]])/n)
  rho <- 0
  df_naive_cov <- sum(nc/(1+(nc-1)*rho))-1
  t_naive_cov <- -qt(0.025,df_naive_cov)
  
  ################################################################################################################################################
  # ========= Fixed-effects estimator without covariates =========
  model_fixed <- fixed_fun(dta,c,trt,y)
  me_var_fixed <- calc_me_var(dta,c,model_fixed,nc)
  coef_fixed_1 <- mean(me_var_fixed[[1]])
  coef_fixed <- mean(me_var_fixed[[3]])
  
  #Estimate tau_square
  fixed_1_tau <- tau_square(me_var_fixed[[1]],me_var_fixed[[2]])
  fixed_tau <- tau_square(me_var_fixed[[3]],me_var_fixed[[4]])
  
  #REML
  se_fixed_1_REML <- sqrt((fixed_1_tau[[1]]+mean(me_var_fixed[[2]]))/k)
  t_fixed_1_REML <- cal_t(fixed_1_tau[[1]],me_var_fixed[[2]],me_var_fixed[[5]])
  se_fixed_REML <- sqrt((fixed_tau[[1]]+mean(me_var_fixed[[4]]))/k)
  t_fixed_REML <- cal_t(fixed_tau[[1]],me_var_fixed[[4]],me_var_fixed[[5]])
  
  #DL
  se_fixed_1_DL <- sqrt((fixed_1_tau[[2]]+mean(me_var_fixed[[2]]))/k)
  t_fixed_1_DL <- cal_t(fixed_1_tau[[2]],me_var_fixed[[2]],me_var_fixed[[5]])
  se_fixed_DL <- sqrt((fixed_tau[[2]]+mean(me_var_fixed[[4]]))/k)
  t_fixed_DL <- cal_t(fixed_tau[[2]],me_var_fixed[[4]],me_var_fixed[[5]])
  
  #Adapted
  se_fixed_1_AD <- sqrt((fixed_1_tau[[3]]+mean(me_var_fixed[[2]]))/k)
  t_fixed_1_AD <- cal_t(fixed_1_tau[[3]],me_var_fixed[[2]],me_var_fixed[[5]])
  se_fixed_AD <- sqrt((fixed_tau[[3]]+mean(me_var_fixed[[4]]))/k)
  t_fixed_AD <- cal_t(fixed_tau[[3]],me_var_fixed[[4]],me_var_fixed[[5]])
  
  ################################################################################################################################################
  # ========= Fixed-effects estimator with covariates =========
  model_fixed_cov <- fixed_cov_fun(dta,c,trt,x1,x2,x3,x4,y)
  me_var_fixed_cov <- calc_me_var(dta,c,model_fixed_cov,nc)
  coef_fixed_1_cov <- mean(me_var_fixed_cov[[1]])
  coef_fixed_cov <- mean(me_var_fixed_cov[[3]])
  
  #Estimate tau_square
  fixed_1_cov_tau <- tau_square(me_var_fixed_cov[[1]],me_var_fixed_cov[[2]])
  fixed_cov_tau <- tau_square(me_var_fixed_cov[[3]],me_var_fixed_cov[[4]])
  
  #REML
  se_fixed_1_cov_REML <- sqrt((fixed_1_cov_tau[[1]]+mean(me_var_fixed_cov[[2]]))/k)
  t_fixed_1_cov_REML <- cal_t(fixed_1_cov_tau[[1]],me_var_fixed_cov[[2]],me_var_fixed_cov[[5]])
  se_fixed_cov_REML <- sqrt((fixed_cov_tau[[1]]+mean(me_var_fixed_cov[[4]]))/k)
  t_fixed_cov_REML <- cal_t(fixed_cov_tau[[1]],me_var_fixed_cov[[4]],me_var_fixed_cov[[5]])
  
  #DL
  se_fixed_1_cov_DL <- sqrt((fixed_1_cov_tau[[2]]+mean(me_var_fixed_cov[[2]]))/k)
  t_fixed_1_cov_DL <- cal_t(fixed_1_cov_tau[[2]],me_var_fixed_cov[[2]],me_var_fixed_cov[[5]])
  se_fixed_cov_DL <- sqrt((fixed_cov_tau[[2]]+mean(me_var_fixed_cov[[4]]))/k)
  t_fixed_cov_DL <- cal_t(fixed_cov_tau[[2]],me_var_fixed_cov[[4]],me_var_fixed_cov[[5]])
  
  #Adapted
  se_fixed_1_cov_AD <- sqrt((fixed_1_cov_tau[[3]]+mean(me_var_fixed_cov[[2]]))/k)
  t_fixed_1_cov_AD <- cal_t(fixed_1_cov_tau[[3]],me_var_fixed_cov[[2]],me_var_fixed_cov[[5]])
  se_fixed_cov_AD <- sqrt((fixed_cov_tau[[3]]+mean(me_var_fixed_cov[[4]]))/k)
  t_fixed_cov_AD <- cal_t(fixed_cov_tau[[3]],me_var_fixed_cov[[4]],me_var_fixed_cov[[5]])
  
  ################################################################################################################################################
  # ========= Random-effects estimates using empirical BLUPs =========
  #Mixed
  model_mixed <- mixed_fun(dta,c,trt,y)
  me_var_mixed <- calc_me_var(dta,c,model_mixed,nc)
  coef_mixed_1 <- mean(me_var_mixed[[1]])
  coef_mixed <- mean(me_var_mixed[[3]])
  
  #Estimate tau_square
  mixed_1_tau <- tau_square(me_var_mixed[[1]],me_var_mixed[[2]])
  mixed_tau <- tau_square(me_var_mixed[[3]],me_var_mixed[[4]])
  
  #REML
  se_mixed_1_REML <- sqrt((mixed_1_tau[[1]]+mean(me_var_mixed[[2]]))/k)
  t_mixed_1_REML <- cal_t(mixed_1_tau[[1]],me_var_mixed[[2]],me_var_mixed[[5]])
  se_mixed_REML <- sqrt((mixed_tau[[1]]+mean(me_var_mixed[[4]]))/k)
  t_mixed_REML <- cal_t(mixed_tau[[1]],me_var_mixed[[4]],me_var_mixed[[5]])
  
  #DL
  se_mixed_1_DL <- sqrt((mixed_1_tau[[2]]+mean(me_var_mixed[[2]]))/k)
  t_mixed_1_DL <- cal_t(mixed_1_tau[[2]],me_var_mixed[[2]],me_var_mixed[[5]])
  se_mixed_DL <- sqrt((mixed_tau[[2]]+mean(me_var_mixed[[4]]))/k)
  t_mixed_DL <- cal_t(mixed_tau[[2]],me_var_mixed[[4]],me_var_mixed[[5]])
  
  #Adapted
  se_mixed_1_AD <- sqrt((mixed_1_tau[[3]]+mean(me_var_mixed[[2]]))/k)
  t_mixed_1_AD <- cal_t(mixed_1_tau[[3]],me_var_mixed[[2]],me_var_mixed[[5]])
  se_mixed_AD <- sqrt((mixed_tau[[3]]+mean(me_var_mixed[[4]]))/k)
  t_mixed_AD <- cal_t(mixed_tau[[3]],me_var_mixed[[4]],me_var_mixed[[5]])
  
  #Mixed_cov
  model_mixed_cov <- mixed_cov_fun(dta,c,trt,x1,x2,x3,x4,y)
  me_var_mixed_cov <- calc_me_var(dta,c,model_mixed_cov,nc)
  coef_mixed_1_cov <- mean(me_var_mixed_cov[[1]])
  coef_mixed_cov <- mean(me_var_mixed_cov[[3]])
  
  #Estimate tau_square
  mixed_1_cov_tau <- tau_square(me_var_mixed_cov[[1]],me_var_mixed_cov[[2]])
  mixed_cov_tau <- tau_square(me_var_mixed_cov[[3]],me_var_mixed_cov[[4]])
  
  #REML
  se_mixed_1_cov_REML <- sqrt((mixed_1_cov_tau[[1]]+mean(me_var_mixed_cov[[2]]))/k)
  t_mixed_1_cov_REML <- cal_t(mixed_1_cov_tau[[1]],me_var_mixed_cov[[2]],me_var_mixed_cov[[5]])
  se_mixed_cov_REML <- sqrt((mixed_cov_tau[[1]]+mean(me_var_mixed_cov[[4]]))/k)
  t_mixed_cov_REML <- cal_t(mixed_cov_tau[[1]],me_var_mixed_cov[[4]],me_var_mixed_cov[[5]])
  
  #DL
  se_mixed_1_cov_DL <- sqrt((mixed_1_cov_tau[[2]]+mean(me_var_mixed_cov[[2]]))/k)
  t_mixed_1_cov_DL <- cal_t(mixed_1_cov_tau[[2]],me_var_mixed_cov[[2]],me_var_mixed_cov[[5]])
  se_mixed_cov_DL <- sqrt((mixed_cov_tau[[2]]+mean(me_var_mixed_cov[[4]]))/k)
  t_mixed_cov_DL <- cal_t(mixed_cov_tau[[2]],me_var_mixed_cov[[4]],me_var_mixed_cov[[5]])
  
  #Adapted
  se_mixed_1_cov_AD <- sqrt((mixed_1_cov_tau[[3]]+mean(me_var_mixed_cov[[2]]))/k)
  t_mixed_1_cov_AD <- cal_t(mixed_1_cov_tau[[3]],me_var_mixed_cov[[2]],me_var_mixed_cov[[5]])
  se_mixed_cov_AD <- sqrt((mixed_cov_tau[[3]]+mean(me_var_mixed_cov[[4]]))/k)
  t_mixed_cov_AD <- cal_t(mixed_cov_tau[[3]],me_var_mixed_cov[[4]],me_var_mixed_cov[[5]])
  
  #Mixed_slope
  model_mixed_slope <- mixed_slope_fun(dta,c,trt,y)
  me_var_mixed_slope <- calc_me_var(dta,c,model_mixed_slope,nc)
  coef_mixed_1_slope <- mean(me_var_mixed_slope[[1]])
  coef_mixed_slope <- mean(me_var_mixed_slope[[3]])
  
  #Estimate tau_square
  mixed_1_slope_tau <- tau_square(me_var_mixed_slope[[1]],me_var_mixed_slope[[2]])
  mixed_slope_tau <- tau_square(me_var_mixed_slope[[3]],me_var_mixed_slope[[4]])
  
  #REML
  se_mixed_1_slope_REML <- sqrt((mixed_1_slope_tau[[1]]+mean(me_var_mixed_slope[[2]]))/k)
  t_mixed_1_slope_REML <- cal_t(mixed_1_slope_tau[[1]],me_var_mixed_slope[[2]],me_var_mixed_slope[[5]])
  se_mixed_slope_REML <- sqrt((mixed_slope_tau[[1]]+mean(me_var_mixed_slope[[4]]))/k)
  t_mixed_slope_REML <- cal_t(mixed_slope_tau[[1]],me_var_mixed_slope[[4]],me_var_mixed_slope[[5]])
  
  #DL
  se_mixed_1_slope_DL <- sqrt((mixed_1_slope_tau[[2]]+mean(me_var_mixed_slope[[2]]))/k)
  t_mixed_1_slope_DL <- cal_t(mixed_1_slope_tau[[2]],me_var_mixed_slope[[2]],me_var_mixed_slope[[5]])
  se_mixed_slope_DL <- sqrt((mixed_slope_tau[[2]]+mean(me_var_mixed_slope[[4]]))/k)
  t_mixed_slope_DL <- cal_t(mixed_slope_tau[[2]],me_var_mixed_slope[[4]],me_var_mixed_slope[[5]])
  
  #Adapted
  se_mixed_1_slope_AD <- sqrt((mixed_1_slope_tau[[3]]+mean(me_var_mixed_slope[[2]]))/k)
  t_mixed_1_slope_AD <- cal_t(mixed_1_slope_tau[[3]],me_var_mixed_slope[[2]],me_var_mixed_slope[[5]])
  se_mixed_slope_AD <- sqrt((mixed_slope_tau[[3]]+mean(me_var_mixed_slope[[4]]))/k)
  t_mixed_slope_AD <- cal_t(mixed_slope_tau[[3]],me_var_mixed_slope[[4]],me_var_mixed_slope[[5]])
  
  #Mixed_cov_slope
  model_mixed_cov_slope <- mixed_cov_slope_fun(dta,c,trt,x1,x2,x3,x4,y)
  me_var_mixed_cov_slope <- calc_me_var(dta,c,model_mixed_cov_slope,nc)
  coef_mixed_1_cov_slope <- mean(me_var_mixed_cov_slope[[1]])
  coef_mixed_cov_slope <- mean(me_var_mixed_cov_slope[[3]])
  
  #Estimate tau_square
  mixed_1_cov_slope_tau <- tau_square(me_var_mixed_cov_slope[[1]],me_var_mixed_cov_slope[[2]])
  mixed_cov_slope_tau <- tau_square(me_var_mixed_cov_slope[[3]],me_var_mixed_cov_slope[[4]])
  
  #REML
  se_mixed_1_cov_slope_REML <- sqrt((mixed_1_cov_slope_tau[[1]]+mean(me_var_mixed_cov_slope[[2]]))/k)
  t_mixed_1_cov_slope_REML <- cal_t(mixed_1_cov_slope_tau[[1]],me_var_mixed_cov_slope[[2]],me_var_mixed_cov_slope[[5]])
  se_mixed_cov_slope_REML <- sqrt((mixed_cov_slope_tau[[1]]+mean(me_var_mixed_cov_slope[[4]]))/k)
  t_mixed_cov_slope_REML <- cal_t(mixed_cov_slope_tau[[1]],me_var_mixed_cov_slope[[4]],me_var_mixed_cov_slope[[5]])
  
  #DL
  se_mixed_1_cov_slope_DL <- sqrt((mixed_1_cov_slope_tau[[2]]+mean(me_var_mixed_cov_slope[[2]]))/k)
  t_mixed_1_cov_slope_DL <- cal_t(mixed_1_cov_slope_tau[[2]],me_var_mixed_cov_slope[[2]],me_var_mixed_cov_slope[[5]])
  se_mixed_cov_slope_DL <- sqrt((mixed_cov_slope_tau[[2]]+mean(me_var_mixed_cov_slope[[4]]))/k)
  t_mixed_cov_slope_DL <- cal_t(mixed_cov_slope_tau[[2]],me_var_mixed_cov_slope[[4]],me_var_mixed_cov_slope[[5]])
  
  #Adapted
  se_mixed_1_cov_slope_AD <- sqrt((mixed_1_cov_slope_tau[[3]]+mean(me_var_mixed_cov_slope[[2]]))/k)
  t_mixed_1_cov_slope_AD <- cal_t(mixed_1_cov_slope_tau[[3]],me_var_mixed_cov_slope[[2]],me_var_mixed_cov_slope[[5]])
  se_mixed_cov_slope_AD <- sqrt((mixed_cov_slope_tau[[3]]+mean(me_var_mixed_cov_slope[[4]]))/k)
  t_mixed_cov_slope_AD <- cal_t(mixed_cov_slope_tau[[3]],me_var_mixed_cov_slope[[4]],me_var_mixed_cov_slope[[5]])
  
  ################################################################################################################################################
  # ========= Random-effects estimates drawing from normal distribution using the estimated random-effects variance =========
  #Mixed sampled
  model_mixed_sim <- mixed_simulated_fun(dta,c,trt,y)
  me_var_mixed_sim <- calc_me_var(dta,c,model_mixed_sim,nc)
  coef_mixed_sim_1 <- mean(me_var_mixed_sim[[1]])
  coef_mixed_sim <- mean(me_var_mixed_sim[[3]])
  
  #Estimate tau_square
  mixed_sim_1_tau <- tau_square(me_var_mixed_sim[[1]],me_var_mixed_sim[[2]])
  mixed_sim_tau <- tau_square(me_var_mixed_sim[[3]],me_var_mixed_sim[[4]])
  
  #REML
  se_mixed_sim_1_REML <- sqrt((mixed_sim_1_tau[[1]]+mean(me_var_mixed_sim[[2]]))/k)
  t_mixed_sim_1_REML <- cal_t(mixed_sim_1_tau[[1]],me_var_mixed_sim[[2]],me_var_mixed_sim[[5]])
  se_mixed_sim_REML <- sqrt((mixed_sim_tau[[1]]+mean(me_var_mixed_sim[[4]]))/k)
  t_mixed_sim_REML <- cal_t(mixed_sim_tau[[1]],me_var_mixed_sim[[4]],me_var_mixed_sim[[5]])
  
  #DL
  se_mixed_sim_1_DL <- sqrt((mixed_sim_1_tau[[2]]+mean(me_var_mixed_sim[[2]]))/k)
  t_mixed_sim_1_DL <- cal_t(mixed_sim_1_tau[[2]],me_var_mixed_sim[[2]],me_var_mixed_sim[[5]])
  se_mixed_sim_DL <- sqrt((mixed_sim_tau[[2]]+mean(me_var_mixed_sim[[4]]))/k)
  t_mixed_sim_DL <- cal_t(mixed_sim_tau[[2]],me_var_mixed_sim[[4]],me_var_mixed_sim[[5]])
  
  #Adapted
  se_mixed_sim_1_AD <- sqrt((mixed_sim_1_tau[[3]]+mean(me_var_mixed_sim[[2]]))/k)
  t_mixed_sim_1_AD <- cal_t(mixed_sim_1_tau[[3]],me_var_mixed_sim[[2]],me_var_mixed_sim[[5]])
  se_mixed_sim_AD <- sqrt((mixed_sim_tau[[3]]+mean(me_var_mixed_sim[[4]]))/k)
  t_mixed_sim_AD <- cal_t(mixed_sim_tau[[3]],me_var_mixed_sim[[4]],me_var_mixed_sim[[5]])
  
  #Mixed_cov sampled
  model_mixed_cov_sim <- mixed_cov_simulated(dta,c,trt,x1,x2,x3,x4,y)
  me_var_mixed_cov_sim <- calc_me_var(dta,c,model_mixed_cov_sim,nc)
  coef_mixed_sim_1_cov <- mean(me_var_mixed_cov_sim[[1]])
  coef_mixed_sim_cov <- mean(me_var_mixed_cov_sim[[3]])
  
  #Estimate tau_square
  mixed_sim_1_cov_tau <- tau_square(me_var_mixed_cov_sim[[1]],me_var_mixed_cov_sim[[2]])
  mixed_sim_cov_tau <- tau_square(me_var_mixed_cov_sim[[3]],me_var_mixed_cov_sim[[4]])
  
  #REML
  se_mixed_sim_1_cov_REML <- sqrt((mixed_sim_1_cov_tau[[1]]+mean(me_var_mixed_cov_sim[[2]]))/k)
  t_mixed_sim_1_cov_REML <- cal_t(mixed_sim_1_cov_tau[[1]],me_var_mixed_cov_sim[[2]],me_var_mixed_cov_sim[[5]])
  se_mixed_sim_cov_REML <- sqrt((mixed_sim_cov_tau[[1]]+mean(me_var_mixed_cov_sim[[4]]))/k)
  t_mixed_sim_cov_REML <- cal_t(mixed_sim_cov_tau[[1]],me_var_mixed_cov_sim[[4]],me_var_mixed_cov_sim[[5]])
  
  #DL
  se_mixed_sim_1_cov_DL <- sqrt((mixed_sim_1_cov_tau[[2]]+mean(me_var_mixed_cov_sim[[2]]))/k)
  t_mixed_sim_1_cov_DL <- cal_t(mixed_sim_1_cov_tau[[2]],me_var_mixed_cov_sim[[2]],me_var_mixed_cov_sim[[5]])
  se_mixed_sim_cov_DL <- sqrt((mixed_sim_cov_tau[[2]]+mean(me_var_mixed_cov_sim[[4]]))/k)
  t_mixed_sim_cov_DL <- cal_t(mixed_sim_cov_tau[[2]],me_var_mixed_cov_sim[[4]],me_var_mixed_cov_sim[[5]])
  
  #Adapted
  se_mixed_sim_1_cov_AD <- sqrt((mixed_sim_1_cov_tau[[3]]+mean(me_var_mixed_cov_sim[[2]]))/k)
  t_mixed_sim_1_cov_AD <- cal_t(mixed_sim_1_cov_tau[[3]],me_var_mixed_cov_sim[[2]],me_var_mixed_cov_sim[[5]])
  se_mixed_sim_cov_AD <- sqrt((mixed_sim_cov_tau[[3]]+mean(me_var_mixed_cov_sim[[4]]))/k)
  t_mixed_sim_cov_AD <- cal_t(mixed_sim_cov_tau[[3]],me_var_mixed_cov_sim[[4]],me_var_mixed_cov_sim[[5]])
  
  #Mixed_slope sampled
  model_mixed_slope_sim <- model_slope_fun(dta,c,trt,y)
  me_var_mixed_slope_sim <- calc_me_var(dta,c,model_mixed_slope_sim,nc)
  coef_mixed_sim_1_slope <- mean(me_var_mixed_slope_sim[[1]])
  coef_mixed_sim_slope <- mean(me_var_mixed_slope_sim[[3]])
  
  #Estimate tau_square
  mixed_sim_1_slope_tau <- tau_square(me_var_mixed_slope_sim[[1]],me_var_mixed_slope_sim[[2]])
  mixed_sim_slope_tau <- tau_square(me_var_mixed_slope_sim[[3]],me_var_mixed_slope_sim[[4]])
  
  #REML
  se_mixed_sim_1_slope_REML <- sqrt((mixed_sim_1_slope_tau[[1]]+mean(me_var_mixed_slope_sim[[2]]))/k)
  t_mixed_sim_1_slope_REML <- cal_t(mixed_sim_1_slope_tau[[1]],me_var_mixed_slope_sim[[2]],me_var_mixed_slope_sim[[5]])
  se_mixed_sim_slope_REML <- sqrt((mixed_sim_slope_tau[[1]]+mean(me_var_mixed_slope_sim[[4]]))/k)
  t_mixed_sim_slope_REML <- cal_t(mixed_sim_slope_tau[[1]],me_var_mixed_slope_sim[[4]],me_var_mixed_slope_sim[[5]])
  
  #DL
  se_mixed_sim_1_slope_DL <- sqrt((mixed_sim_1_slope_tau[[2]]+mean(me_var_mixed_slope_sim[[2]]))/k)
  t_mixed_sim_1_slope_DL <- cal_t(mixed_sim_1_slope_tau[[2]],me_var_mixed_slope_sim[[2]],me_var_mixed_slope_sim[[5]])
  se_mixed_sim_slope_DL <- sqrt((mixed_sim_slope_tau[[2]]+mean(me_var_mixed_slope_sim[[4]]))/k)
  t_mixed_sim_slope_DL <- cal_t(mixed_sim_slope_tau[[2]],me_var_mixed_slope_sim[[4]],me_var_mixed_slope_sim[[5]])
  
  #Adapted
  se_mixed_sim_1_slope_AD <- sqrt((mixed_sim_1_slope_tau[[3]]+mean(me_var_mixed_slope_sim[[2]]))/k)
  t_mixed_sim_1_slope_AD <- cal_t(mixed_sim_1_slope_tau[[3]],me_var_mixed_slope_sim[[2]],me_var_mixed_slope_sim[[5]])
  se_mixed_sim_slope_AD <- sqrt((mixed_sim_slope_tau[[3]]+mean(me_var_mixed_slope_sim[[4]]))/k)
  t_mixed_sim_slope_AD <- cal_t(mixed_sim_slope_tau[[3]],me_var_mixed_slope_sim[[4]],me_var_mixed_slope_sim[[5]])
  
  #Mixed_cov_slope sampled
  model_mixed_cov_slope_sim <- mixed_cov_slope_simulated_fun(dta,c,trt,x1,x2,x3,x4,y)
  me_var_mixed_cov_slope_sim <- calc_me_var(dta,c,model_mixed_cov_slope_sim,nc)
  coef_mixed_sim_1_cov_slope <- mean(me_var_mixed_cov_slope_sim[[1]])
  coef_mixed_sim_cov_slope <- mean(me_var_mixed_cov_slope_sim[[3]])
  
  #Estimate tau_square
  mixed_sim_1_cov_slope_tau <- tau_square(me_var_mixed_cov_slope_sim[[1]],me_var_mixed_cov_slope_sim[[2]])
  mixed_sim_cov_slope_tau <- tau_square(me_var_mixed_cov_slope_sim[[3]],me_var_mixed_cov_slope_sim[[4]])
  
  #REML
  se_mixed_sim_1_cov_slope_REML <- sqrt((mixed_sim_1_cov_slope_tau[[1]]+mean(me_var_mixed_cov_slope_sim[[2]]))/k)
  t_mixed_sim_1_cov_slope_REML <- cal_t(mixed_sim_1_cov_slope_tau[[1]],me_var_mixed_cov_slope_sim[[2]],me_var_mixed_cov_slope_sim[[5]])
  se_mixed_sim_cov_slope_REML <- sqrt((mixed_sim_cov_slope_tau[[1]]+mean(me_var_mixed_cov_slope_sim[[4]]))/k)
  t_mixed_sim_cov_slope_REML <- cal_t(mixed_sim_cov_slope_tau[[1]],me_var_mixed_cov_slope_sim[[4]],me_var_mixed_cov_slope_sim[[5]])
  
  #DL
  se_mixed_sim_1_cov_slope_DL <- sqrt((mixed_sim_1_cov_slope_tau[[2]]+mean(me_var_mixed_cov_slope_sim[[2]]))/k)
  t_mixed_sim_1_cov_slope_DL <- cal_t(mixed_sim_1_cov_slope_tau[[2]],me_var_mixed_cov_slope_sim[[2]],me_var_mixed_cov_slope_sim[[5]])
  se_mixed_sim_cov_slope_DL <- sqrt((mixed_sim_cov_slope_tau[[2]]+mean(me_var_mixed_cov_slope_sim[[4]]))/k)
  t_mixed_sim_cov_slope_DL <- cal_t(mixed_sim_cov_slope_tau[[2]],me_var_mixed_cov_slope_sim[[4]],me_var_mixed_cov_slope_sim[[5]])
  
  #Adapted
  se_mixed_sim_1_cov_slope_AD <- sqrt((mixed_sim_1_cov_slope_tau[[3]]+mean(me_var_mixed_cov_slope_sim[[2]]))/k)
  t_mixed_sim_1_cov_slope_AD <- cal_t(mixed_sim_1_cov_slope_tau[[3]],me_var_mixed_cov_slope_sim[[2]],me_var_mixed_cov_slope_sim[[5]])
  se_mixed_sim_cov_slope_AD <- sqrt((mixed_sim_cov_slope_tau[[3]]+mean(me_var_mixed_cov_slope_sim[[4]]))/k)
  t_mixed_sim_cov_slope_AD <- cal_t(mixed_sim_cov_slope_tau[[3]],me_var_mixed_cov_slope_sim[[4]],me_var_mixed_cov_slope_sim[[5]])
  
  ################################################################################################################################################
  
  return(list(
    "coef_naive_1"=coef_naive_1,"se_naive_1"=se_naive_1,"t_naive"=t_naive,
    "coef_naive"=coef_naive,"se_naive"=se_naive,
    
    "coef_naive_1_cov"=coef_naive_1_cov,"se_naive_1_cov"=se_naive_1_cov,"t_naive_cov"=t_naive_cov,
    "coef_naive_cov"=coef_naive_cov,"se_naive_cov"=se_naive_cov,
    
    "coef_fixed_1"=coef_fixed_1,"se_fixed_1_REML"=se_fixed_1_REML,"se_fixed_1_DL"=se_fixed_1_DL,"se_fixed_1_AD"=se_fixed_1_AD,
    "t_fixed_1_REML"=t_fixed_1_REML,"t_fixed_1_DL"=t_fixed_1_DL,"t_fixed_1_AD"=t_fixed_1_AD,
    "coef_fixed"=coef_fixed,"se_fixed_REML"=se_fixed_REML,"se_fixed_DL"=se_fixed_DL,"se_fixed_AD"=se_fixed_AD,
    "t_fixed_REML"=t_fixed_REML,"t_fixed_DL"=t_fixed_DL,"t_fixed_AD"=t_fixed_AD,
    
    "coef_fixed_1_cov"=coef_fixed_1_cov,"se_fixed_1_cov_REML"=se_fixed_1_cov_REML,"se_fixed_1_cov_DL"=se_fixed_1_cov_DL,"se_fixed_1_cov_AD"=se_fixed_1_cov_AD,
    "t_fixed_1_cov_REML"=t_fixed_1_cov_REML,"t_fixed_1_cov_DL"=t_fixed_1_cov_DL,"t_fixed_1_cov_AD"=t_fixed_1_cov_AD,
    "coef_fixed_cov"=coef_fixed_cov,"se_fixed_cov_REML"=se_fixed_cov_REML,"se_fixed_cov_DL"=se_fixed_cov_DL,"se_fixed_cov_AD"=se_fixed_cov_AD,
    "t_fixed_cov_REML"=t_fixed_cov_REML,"t_fixed_cov_DL"=t_fixed_cov_DL,"t_fixed_cov_AD"=t_fixed_cov_AD,
    
    "coef_mixed_1"=coef_mixed_1,"se_mixed_1_REML"=se_mixed_1_REML,"se_mixed_1_DL"=se_mixed_1_DL,"se_mixed_1_AD"=se_mixed_1_AD,
    "t_mixed_1_REML"=t_mixed_1_REML,"t_mixed_1_DL"=t_mixed_1_DL,"t_mixed_1_AD"=t_mixed_1_AD,
    "coef_mixed"=coef_mixed,"se_mixed_REML"=se_mixed_REML,"se_mixed_DL"=se_mixed_DL,"se_mixed_AD"=se_mixed_AD,
    "t_mixed_REML"=t_mixed_REML,"t_mixed_DL"=t_mixed_DL,"t_mixed_AD"=t_mixed_AD,
    
    "coef_mixed_1_cov"=coef_mixed_1_cov,"se_mixed_1_cov_REML"=se_mixed_1_cov_REML,"se_mixed_1_cov_DL"=se_mixed_1_cov_DL,"se_mixed_1_cov_AD"=se_mixed_1_cov_AD,
    "t_mixed_1_cov_REML"=t_mixed_1_cov_REML,"t_mixed_1_cov_DL"=t_mixed_1_cov_DL,"t_mixed_1_cov_AD"=t_mixed_1_cov_AD,
    "coef_mixed_cov"=coef_mixed_cov,"se_mixed_cov_REML"=se_mixed_cov_REML,"se_mixed_cov_DL"=se_mixed_cov_DL,"se_mixed_cov_AD"=se_mixed_cov_AD,
    "t_mixed_cov_REML"=t_mixed_cov_REML,"t_mixed_cov_DL"=t_mixed_cov_DL,"t_mixed_cov_AD"=t_mixed_cov_AD,
    
    "coef_mixed_1_slope"=coef_mixed_1_slope,"se_mixed_1_slope_REML"=se_mixed_1_slope_REML,"se_mixed_1_slope_DL"=se_mixed_1_slope_DL,"se_mixed_1_slope_AD"=se_mixed_1_slope_AD,
    "t_mixed_1_slope_REML"=t_mixed_1_slope_REML,"t_mixed_1_slope_DL"=t_mixed_1_slope_DL,"t_mixed_1_slope_AD"=t_mixed_1_slope_AD,
    "coef_mixed_slope"=coef_mixed_slope,"se_mixed_slope_REML"=se_mixed_slope_REML,"se_mixed_slope_DL"=se_mixed_slope_DL,"se_mixed_slope_AD"=se_mixed_slope_AD,
    "t_mixed_slope_REML"=t_mixed_slope_REML,"t_mixed_slope_DL"=t_mixed_slope_DL,"t_mixed_slope_AD"=t_mixed_slope_AD,
    
    "coef_mixed_1_cov_slope"=coef_mixed_1_cov_slope,"se_mixed_1_cov_slope_REML"=se_mixed_1_cov_slope_REML,"se_mixed_1_cov_slope_DL"=se_mixed_1_cov_slope_DL,"se_mixed_1_cov_slope_AD"=se_mixed_1_cov_slope_AD,
    "t_mixed_1_cov_slope_REML"=t_mixed_1_cov_slope_REML,"t_mixed_1_cov_slope_DL"=t_mixed_1_cov_slope_DL,"t_mixed_1_cov_slope_AD"=t_mixed_1_cov_slope_AD,
    "coef_mixed_cov_slope"=coef_mixed_cov_slope,"se_mixed_cov_slope_REML"=se_mixed_cov_slope_REML,"se_mixed_cov_slope_DL"=se_mixed_cov_slope_DL,"se_mixed_cov_slope_AD"=se_mixed_cov_slope_AD,
    "t_mixed_cov_slope_REML"=t_mixed_cov_slope_REML,"t_mixed_cov_slope_DL"=t_mixed_cov_slope_DL,"t_mixed_cov_slope_AD"=t_mixed_cov_slope_AD,
    
    "coef_mixed_sim_1"=coef_mixed_sim_1,"se_mixed_sim_1_REML"=se_mixed_sim_1_REML,"se_mixed_sim_1_DL"=se_mixed_sim_1_DL,"se_mixed_sim_1_AD"=se_mixed_sim_1_AD,
    "t_mixed_sim_1_REML"=t_mixed_sim_1_REML,"t_mixed_sim_1_DL"=t_mixed_sim_1_DL,"t_mixed_sim_1_AD"=t_mixed_sim_1_AD,
    "coef_mixed_sim"=coef_mixed_sim,"se_mixed_sim_REML"=se_mixed_sim_REML,"se_mixed_sim_DL"=se_mixed_sim_DL,"se_mixed_sim_AD"=se_mixed_sim_AD,
    "t_mixed_sim_REML"=t_mixed_sim_REML,"t_mixed_sim_DL"=t_mixed_sim_DL,"t_mixed_sim_AD"=t_mixed_sim_AD,
    
    "coef_mixed_sim_1_cov"=coef_mixed_sim_1_cov,"se_mixed_sim_1_cov_REML"=se_mixed_sim_1_cov_REML,"se_mixed_sim_1_cov_DL"=se_mixed_sim_1_cov_DL,"se_mixed_sim_1_cov_AD"=se_mixed_sim_1_cov_AD,
    "t_mixed_sim_1_cov_REML"=t_mixed_sim_1_cov_REML,"t_mixed_sim_1_cov_DL"=t_mixed_sim_1_cov_DL,"t_mixed_sim_1_cov_AD"=t_mixed_sim_1_cov_AD,
    "coef_mixed_sim_cov"=coef_mixed_sim_cov,"se_mixed_sim_cov_REML"=se_mixed_sim_cov_REML,"se_mixed_sim_cov_DL"=se_mixed_sim_cov_DL,"se_mixed_sim_cov_AD"=se_mixed_sim_cov_AD,
    "t_mixed_sim_cov_REML"=t_mixed_sim_cov_REML,"t_mixed_sim_cov_DL"=t_mixed_sim_cov_DL,"t_mixed_sim_cov_AD"=t_mixed_sim_cov_AD,
    
    "coef_mixed_sim_1_slope"=coef_mixed_sim_1_slope,"se_mixed_sim_1_slope_REML"=se_mixed_sim_1_slope_REML,"se_mixed_sim_1_slope_DL"=se_mixed_sim_1_slope_DL,"se_mixed_sim_1_slope_AD"=se_mixed_sim_1_slope_AD,
    "t_mixed_sim_1_slope_REML"=t_mixed_sim_1_slope_REML,"t_mixed_sim_1_slope_DL"=t_mixed_sim_1_slope_DL,"t_mixed_sim_1_slope_AD"=t_mixed_sim_1_slope_AD,
    "coef_mixed_sim_slope"=coef_mixed_sim_slope,"se_mixed_sim_slope_REML"=se_mixed_sim_slope_REML,"se_mixed_sim_slope_DL"=se_mixed_sim_slope_DL,"se_mixed_sim_slope_AD"=se_mixed_sim_slope_AD,
    "t_mixed_sim_slope_REML"=t_mixed_sim_slope_REML,"t_mixed_sim_slope_DL"=t_mixed_sim_slope_DL,"t_mixed_sim_slope_AD"=t_mixed_sim_slope_AD,
    
    "coef_mixed_sim_1_cov_slope"=coef_mixed_sim_1_cov_slope,"se_mixed_sim_1_cov_slope_REML"=se_mixed_sim_1_cov_slope_REML,"se_mixed_sim_1_cov_slope_DL"=se_mixed_sim_1_cov_slope_DL,"se_mixed_sim_1_cov_slope_AD"=se_mixed_sim_1_cov_slope_AD,
    "t_mixed_sim_1_cov_slope_REML"=t_mixed_sim_1_cov_slope_REML,"t_mixed_sim_1_cov_slope_DL"=t_mixed_sim_1_cov_slope_DL,"t_mixed_sim_1_cov_slope_AD"=t_mixed_sim_1_cov_slope_AD,
    "coef_mixed_sim_cov_slope"=coef_mixed_sim_cov_slope,"se_mixed_sim_cov_slope_REML"=se_mixed_sim_cov_slope_REML,"se_mixed_sim_cov_slope_DL"=se_mixed_sim_cov_slope_DL,"se_mixed_sim_cov_slope_AD"=se_mixed_sim_cov_slope_AD,
    "t_mixed_sim_cov_slope_REML"=t_mixed_sim_cov_slope_REML,"t_mixed_sim_cov_slope_DL"=t_mixed_sim_cov_slope_DL,"t_mixed_sim_cov_slope_AD"=t_mixed_sim_cov_slope_AD
  ))
}

#################################################################################################################
#Specify simulation settings
simulate_settings <- function(nrep, setting_params) {
  results <- list()
  for (i in 1:length(setting_params)) {
    params <- setting_params[[i]]
    setting_results <- vector("list",length=nrep)
    for (j in 1:nrep) {
      setting_results[[j]] <- Simulation_function(params$k, params$nc, params$sigma_sequare_u0,
                                                  params$sigma_sequare_u1,params$sigma_sequare_u2)
    }
    results[[i]] <- setting_results
  }
  return(results)
}

#k and nc
k <- 100
nc <- c(1,3,5,2,4,3,3,4,7,5,4,7,1,4,5,8,4,9,1,8,7,6,24,1,3,7,5,6,1,5,2,7,8,1,6,7,4,8,4,10,6,
        7,4,3,2,7,1 ,2 ,3,2,2,1,3,5,2,4,4,3,4,7,5,4,7,1,4,5,8,4,9,3,8,7,4,9,3,7,5,6,9,5,2,7,8,9,6,
        7,4,8,4,10,6,7,4,3,2,6,3,2,3,4)

#Settings
setting_params <- list(
  list(k=k, nc = nc, sigma_sequare_u0=0.75, sigma_sequare_u1= 0.5, sigma_sequare_u2= 0.5))

###Perform simulations
nrep <- 1000
simulation_results <- simulate_settings(nrep, setting_params)

#Manage the simulated data sets
setting_data <- lapply(simulation_results, function(sim_list) {
  do.call(rbind, lapply(sim_list, as.data.frame))
})

result <- setting_data[[1]]

#Optional: save simulated results
#write.csv(result, "all_estimators_simulated_results.csv", row.names = FALSE)

#Optional: instead of running simulation above, read saved results
#result <- read.csv("your_file_path.csv")

nrep<-nrow(result)

theta <- 0.4982133 #true mean outcome under treatment
beta <- 0.05347764 #true mean difference (risk difference)
#################################################################################################################
############################################################################################################
###Bias and MSE
#I:mean outcome under treatment

#Naive
#Bias
bias_coef_naive_1<- as.numeric(result$coef_naive_1)-theta
t.test(bias_coef_naive_1,mu=0)
bias_mean_coef_naive_1 <-mean(as.numeric(result$coef_naive_1))-theta
coef_naive_1 <- as.numeric(result$coef_naive_1)
#MSE
mse_naive_1 <- mean((as.numeric(result$coef_naive_1)-theta)^2)

#Naive_cov
#Bias
bias_coef_naive_1_cov<- as.numeric(result$coef_naive_1_cov)-theta
t.test(bias_coef_naive_1_cov,mu=0)
bias_mean_coef_naive_1_cov <-mean(as.numeric(result$coef_naive_1_cov))-theta
coef_naive_1_cov <- as.numeric(result$coef_naive_1_cov)
#MSE
mse_naive_1_cov <- mean((as.numeric(result$coef_naive_1_cov)-theta)^2)

#Fixed
#Bias
bias_coef_fixed_1<- as.numeric(result$coef_fixed_1)-theta
t.test(bias_coef_fixed_1,mu=0)
bias_mean_coef_fixed_1 <-mean(as.numeric(result$coef_fixed_1))-theta
coef_fixed_1 <- as.numeric(result$coef_fixed_1)
#MSE
mse_fixed_1 <- mean((as.numeric(result$coef_fixed_1)-theta)^2)

#Fixed_cov
#Bias
bias_coef_fixed_1_cov<- as.numeric(result$coef_fixed_1_cov)-theta
t.test(bias_coef_fixed_1_cov,mu=0)
bias_mean_coef_fixed_1_cov <-mean(as.numeric(result$coef_fixed_1_cov))-theta
coef_fixed_1_cov <- as.numeric(result$coef_fixed_1_cov)
#MSE
mse_fixed_1_cov <- mean((as.numeric(result$coef_fixed_1_cov)-theta)^2)

#Mixed BLUP
#Bias
bias_coef_mixed_1<- as.numeric(result$coef_mixed_1)-theta
t.test(bias_coef_mixed_1,mu=0)
bias_mean_coef_mixed_1 <-mean(as.numeric(result$coef_mixed_1))-theta
coef_mixed_1 <- as.numeric(result$coef_mixed_1)
#MSE
mse_mixed_1 <- mean((as.numeric(result$coef_mixed_1)-theta)^2)

#Mixed_cov BLUP
#Bias
bias_coef_mixed_1_cov<- as.numeric(result$coef_mixed_1_cov)-theta
t.test(bias_coef_mixed_1_cov,mu=0)
bias_mean_coef_mixed_1_cov <-mean(as.numeric(result$coef_mixed_1_cov))-theta
coef_mixed_1_cov <- as.numeric(result$coef_mixed_1_cov)
#MSE
mse_mixed_1_cov <- mean((as.numeric(result$coef_mixed_1_cov)-theta)^2)

#Mixed_slope BLUP
#Bias
bias_coef_mixed_1_slope<- as.numeric(result$coef_mixed_1_slope)-theta
t.test(bias_coef_mixed_1_slope,mu=0)
bias_mean_coef_mixed_1_slope <-mean(as.numeric(result$coef_mixed_1_slope))-theta
coef_mixed_1_slope <- as.numeric(result$coef_mixed_1_slope)
#MSE
mse_mixed_1_slope <- mean((as.numeric(result$coef_mixed_1_slope)-theta)^2)

#Mixed_cov_slope BLUP
#Bias
bias_coef_mixed_1_cov_slope<- as.numeric(result$coef_mixed_1_cov_slope)-theta
t.test(bias_coef_mixed_1_cov_slope,mu=0)
bias_mean_coef_mixed_1_cov_slope <-mean(as.numeric(result$coef_mixed_1_cov_slope))-theta
coef_mixed_1_cov_slope <- as.numeric(result$coef_mixed_1_cov_slope)
#MSE
mse_mixed_1_cov_slope <- mean((as.numeric(result$coef_mixed_1_cov_slope)-theta)^2)

#Mixed sampled
#Bias
bias_coef_mixed_sim_1<- as.numeric(result$coef_mixed_sim_1)-theta
t.test(bias_coef_mixed_sim_1,mu=0)
bias_mean_coef_mixed_sim_1 <-mean(as.numeric(result$coef_mixed_sim_1))-theta
coef_mixed_sim_1 <- as.numeric(result$coef_mixed_sim_1)
#MSE
mse_mixed_sim_1 <- mean((as.numeric(result$coef_mixed_sim_1)-theta)^2)

#Mixed_cov sampled
#Bias
bias_coef_mixed_sim_1_cov<- as.numeric(result$coef_mixed_sim_1_cov)-theta
t.test(bias_coef_mixed_sim_1_cov,mu=0)
bias_mean_coef_mixed_sim_1_cov <-mean(as.numeric(result$coef_mixed_sim_1_cov))-theta
coef_mixed_sim_1_cov <- as.numeric(result$coef_mixed_sim_1_cov)
#MSE
mse_mixed_sim_1_cov <- mean((as.numeric(result$coef_mixed_sim_1_cov)-theta)^2)

#Mixed_slope sampled
#Bias
bias_coef_mixed_sim_1_slope<- as.numeric(result$coef_mixed_sim_1_slope)-theta
t.test(bias_coef_mixed_sim_1_slope,mu=0)
bias_mean_coef_mixed_sim_1_slope <-mean(as.numeric(result$coef_mixed_sim_1_slope))-theta
coef_mixed_sim_1_slope <- as.numeric(result$coef_mixed_sim_1_slope)
#MSE
mse_mixed_sim_1_slope <- mean((as.numeric(result$coef_mixed_sim_1_slope)-theta)^2)

#Mixed_cov_slope sampled
#Bias
bias_coef_mixed_sim_1_cov_slope<- as.numeric(result$coef_mixed_sim_1_cov_slope)-theta
t.test(bias_coef_mixed_sim_1_cov_slope,mu=0)
bias_mean_coef_mixed_sim_1_cov_slope <-mean(as.numeric(result$coef_mixed_sim_1_cov_slope))-theta
coef_mixed_sim_1_cov_slope <- as.numeric(result$coef_mixed_sim_1_cov_slope)
#MSE
mse_mixed_sim_1_cov_slope <- mean((as.numeric(result$coef_mixed_sim_1_cov_slope)-theta)^2)

############################################################################################################
#II: mean difference

#Naive
bias_coef_naive<- as.numeric(result$coef_naive)-beta
t.test(bias_coef_naive,mu=0)
bias_mean_coef_naive <-mean(as.numeric(result$coef_naive))-beta
coef_naive <- as.numeric(result$coef_naive)
mse_naive <- mean((as.numeric(result$coef_naive)-beta)^2)

#Naive_cov
bias_coef_naive_cov<- as.numeric(result$coef_naive_cov)-beta
t.test(bias_coef_naive_cov,mu=0)
bias_mean_coef_naive_cov <-mean(as.numeric(result$coef_naive_cov))-beta
coef_naive_cov <- as.numeric(result$coef_naive_cov)
mse_naive_cov <- mean((as.numeric(result$coef_naive_cov)-beta)^2)

#Fixed
bias_coef_fixed<- as.numeric(result$coef_fixed)-beta
t.test(bias_coef_fixed,mu=0)
bias_mean_coef_fixed <-mean(as.numeric(result$coef_fixed))-beta
coef_fixed <- as.numeric(result$coef_fixed)
mse_fixed <- mean((as.numeric(result$coef_fixed)-beta)^2)

#Fixed_cov
bias_coef_fixed_cov<- as.numeric(result$coef_fixed_cov)-beta
t.test(bias_coef_fixed_cov,mu=0)
bias_mean_coef_fixed_cov <-mean(as.numeric(result$coef_fixed_cov))-beta
coef_fixed_cov <- as.numeric(result$coef_fixed_cov)
mse_fixed_cov <- mean((as.numeric(result$coef_fixed_cov)-beta)^2)

#Mixed BLUP
bias_coef_mixed<- as.numeric(result$coef_mixed)-beta
t.test(bias_coef_mixed,mu=0)
bias_mean_coef_mixed <-mean(as.numeric(result$coef_mixed))-beta
coef_mixed <- as.numeric(result$coef_mixed)
mse_mixed <- mean((as.numeric(result$coef_mixed)-beta)^2)

#Mixed_cov BLUP
bias_coef_mixed_cov<- as.numeric(result$coef_mixed_cov)-beta
t.test(bias_coef_mixed_cov,mu=0)
bias_mean_coef_mixed_cov <-mean(as.numeric(result$coef_mixed_cov))-beta
coef_mixed_cov <- as.numeric(result$coef_mixed_cov)
mse_mixed_cov <- mean((as.numeric(result$coef_mixed_cov)-beta)^2)

#Mixed_slope BLUP
bias_coef_mixed_slope<- as.numeric(result$coef_mixed_slope)-beta
t.test(bias_coef_mixed_slope,mu=0)
bias_mean_coef_mixed_slope <-mean(as.numeric(result$coef_mixed_slope))-beta
coef_mixed_slope <- as.numeric(result$coef_mixed_slope)
mse_mixed_slope <- mean((as.numeric(result$coef_mixed_slope)-beta)^2)

#Mixed_cov_slope BLUP
bias_coef_mixed_cov_slope<- as.numeric(result$coef_mixed_cov_slope)-beta
t.test(bias_coef_mixed_cov_slope,mu=0)
bias_mean_coef_mixed_cov_slope <-mean(as.numeric(result$coef_mixed_cov_slope))-beta
coef_mixed_cov_slope <- as.numeric(result$coef_mixed_cov_slope)
mse_mixed_cov_slope <- mean((as.numeric(result$coef_mixed_cov_slope)-beta)^2)

#Mixed sampled
bias_coef_mixed_sim<- as.numeric(result$coef_mixed_sim)-beta
t.test(bias_coef_mixed_sim,mu=0)
bias_mean_coef_mixed_sim <-mean(as.numeric(result$coef_mixed_sim))-beta
coef_mixed_sim <- as.numeric(result$coef_mixed_sim)
mse_mixed_sim <- mean((as.numeric(result$coef_mixed_sim)-beta)^2)

#Mixed_cov sampled
bias_coef_mixed_sim_cov<- as.numeric(result$coef_mixed_sim_cov)-beta
t.test(bias_coef_mixed_sim_cov,mu=0)
bias_mean_coef_mixed_sim_cov <-mean(as.numeric(result$coef_mixed_sim_cov))-beta
coef_mixed_sim_cov <- as.numeric(result$coef_mixed_sim_cov)
mse_mixed_sim_cov <- mean((as.numeric(result$coef_mixed_sim_cov)-beta)^2)

#Mixed_slope sampled
bias_coef_mixed_sim_slope<- as.numeric(result$coef_mixed_sim_slope)-beta
t.test(bias_coef_mixed_sim_slope,mu=0)
bias_mean_coef_mixed_sim_slope <-mean(as.numeric(result$coef_mixed_sim_slope))-beta
coef_mixed_sim_slope <- as.numeric(result$coef_mixed_sim_slope)
mse_mixed_sim_slope <- mean((as.numeric(result$coef_mixed_sim_slope)-beta)^2)

#Mixed_cov_slope sampled
bias_coef_mixed_sim_cov_slope<- as.numeric(result$coef_mixed_sim_cov_slope)-beta
t.test(bias_coef_mixed_sim_cov_slope,mu=0)
bias_mean_coef_mixed_sim_cov_slope <-mean(as.numeric(result$coef_mixed_sim_cov_slope))-beta
coef_mixed_sim_cov_slope <- as.numeric(result$coef_mixed_sim_cov_slope)
mse_mixed_sim_cov_slope <- mean((as.numeric(result$coef_mixed_sim_cov_slope)-beta)^2)

############################################################################################################
#SD and average standard error for counterfactual means

sd_naive_1 <- sqrt(var(result$coef_naive_1))
se_ave_naive_1 <- mean(result$se_naive_1)

sd_naive_1_cov <- sqrt(var(result$coef_naive_1_cov))
se_ave_naive_1_cov <- mean(result$se_naive_1_cov)

sd_fixed_1 <- sqrt(var(result$coef_fixed_1))
se_ave_fixed_1_REML <- mean(result$se_fixed_1_REML)
se_ave_fixed_1_DL <- mean(result$se_fixed_1_DL)
se_ave_fixed_1_AD <- mean(result$se_fixed_1_AD)

sd_fixed_1_cov <- sqrt(var(result$coef_fixed_1_cov))
se_ave_fixed_1_cov_REML <- mean(result$se_fixed_1_cov_REML)
se_ave_fixed_1_cov_DL <- mean(result$se_fixed_1_cov_DL)
se_ave_fixed_1_cov_AD <- mean(result$se_fixed_1_cov_AD)

sd_mixed_1 <- sqrt(var(result$coef_mixed_1))
se_ave_mixed_1_REML <- mean(result$se_mixed_1_REML)
se_ave_mixed_1_DL <- mean(result$se_mixed_1_DL)
se_ave_mixed_1_AD <- mean(result$se_mixed_1_AD)

sd_mixed_1_cov <- sqrt(var(result$coef_mixed_1_cov))
se_ave_mixed_1_cov_REML <- mean(result$se_mixed_1_cov_REML)
se_ave_mixed_1_cov_DL <- mean(result$se_mixed_1_cov_DL)
se_ave_mixed_1_cov_AD <- mean(result$se_mixed_1_cov_AD)

sd_mixed_1_slope <- sqrt(var(result$coef_mixed_1_slope))
se_ave_mixed_1_slope_REML <- mean(result$se_mixed_1_slope_REML)
se_ave_mixed_1_slope_DL <- mean(result$se_mixed_1_slope_DL)
se_ave_mixed_1_slope_AD <- mean(result$se_mixed_1_slope_AD)

sd_mixed_1_cov_slope <- sqrt(var(result$coef_mixed_1_cov_slope))
se_ave_mixed_1_cov_slope_REML <- mean(result$se_mixed_1_cov_slope_REML)
se_ave_mixed_1_cov_slope_DL <- mean(result$se_mixed_1_cov_slope_DL)
se_ave_mixed_1_cov_slope_AD <- mean(result$se_mixed_1_cov_slope_AD)

sd_mixed_sim_1 <- sqrt(var(result$coef_mixed_sim_1))
se_ave_mixed_sim_1_REML <- mean(result$se_mixed_sim_1_REML)
se_ave_mixed_sim_1_DL <- mean(result$se_mixed_sim_1_DL)
se_ave_mixed_sim_1_AD <- mean(result$se_mixed_sim_1_AD)

sd_mixed_sim_1_cov <- sqrt(var(result$coef_mixed_sim_1_cov))
se_ave_mixed_sim_1_cov_REML <- mean(result$se_mixed_sim_1_cov_REML)
se_ave_mixed_sim_1_cov_DL <- mean(result$se_mixed_sim_1_cov_DL)
se_ave_mixed_sim_1_cov_AD <- mean(result$se_mixed_sim_1_cov_AD)

sd_mixed_sim_1_slope <- sqrt(var(result$coef_mixed_sim_1_slope))
se_ave_mixed_sim_1_slope_REML <- mean(result$se_mixed_sim_1_slope_REML)
se_ave_mixed_sim_1_slope_DL <- mean(result$se_mixed_sim_1_slope_DL)
se_ave_mixed_sim_1_slope_AD <- mean(result$se_mixed_sim_1_slope_AD)

sd_mixed_sim_1_cov_slope <- sqrt(var(result$coef_mixed_sim_1_cov_slope))
se_ave_mixed_sim_1_cov_slope_REML <- mean(result$se_mixed_sim_1_cov_slope_REML)
se_ave_mixed_sim_1_cov_slope_DL <- mean(result$se_mixed_sim_1_cov_slope_DL)
se_ave_mixed_sim_1_cov_slope_AD <- mean(result$se_mixed_sim_1_cov_slope_AD)

############################################################################################################
#SD and average standard error for ATE

sd_naive <- sqrt(var(result$coef_naive))
se_ave_naive <- mean(result$se_naive)

sd_naive_cov <- sqrt(var(result$coef_naive_cov))
se_ave_naive_cov <- mean(result$se_naive_cov)

sd_fixed <- sqrt(var(result$coef_fixed))
se_ave_fixed_REML <- mean(result$se_fixed_REML)
se_ave_fixed_DL <- mean(result$se_fixed_DL)
se_ave_fixed_AD <- mean(result$se_fixed_AD)

sd_fixed_cov <- sqrt(var(result$coef_fixed_cov))
se_ave_fixed_cov_REML <- mean(result$se_fixed_cov_REML)
se_ave_fixed_cov_DL <- mean(result$se_fixed_cov_DL)
se_ave_fixed_cov_AD <- mean(result$se_fixed_cov_AD)

sd_mixed <- sqrt(var(result$coef_mixed))
se_ave_mixed_REML <- mean(result$se_mixed_REML)
se_ave_mixed_DL <- mean(result$se_mixed_DL)
se_ave_mixed_AD <- mean(result$se_mixed_AD)

sd_mixed_cov <- sqrt(var(result$coef_mixed_cov))
se_ave_mixed_cov_REML <- mean(result$se_mixed_cov_REML)
se_ave_mixed_cov_DL <- mean(result$se_mixed_cov_DL)
se_ave_mixed_cov_AD <- mean(result$se_mixed_cov_AD)

sd_mixed_slope <- sqrt(var(result$coef_mixed_slope))
se_ave_mixed_slope_REML <- mean(result$se_mixed_slope_REML)
se_ave_mixed_slope_DL <- mean(result$se_mixed_slope_DL)
se_ave_mixed_slope_AD <- mean(result$se_mixed_slope_AD)

sd_mixed_cov_slope <- sqrt(var(result$coef_mixed_cov_slope))
se_ave_mixed_cov_slope_REML <- mean(result$se_mixed_cov_slope_REML)
se_ave_mixed_cov_slope_DL <- mean(result$se_mixed_cov_slope_DL)
se_ave_mixed_cov_slope_AD <- mean(result$se_mixed_cov_slope_AD)

sd_mixed_sim <- sqrt(var(result$coef_mixed_sim))
se_ave_mixed_sim_REML <- mean(result$se_mixed_sim_REML)
se_ave_mixed_sim_DL <- mean(result$se_mixed_sim_DL)
se_ave_mixed_sim_AD <- mean(result$se_mixed_sim_AD)

sd_mixed_sim_cov <- sqrt(var(result$coef_mixed_sim_cov))
se_ave_mixed_sim_cov_REML <- mean(result$se_mixed_sim_cov_REML)
se_ave_mixed_sim_cov_DL <- mean(result$se_mixed_sim_cov_DL)
se_ave_mixed_sim_cov_AD <- mean(result$se_mixed_sim_cov_AD)

sd_mixed_sim_slope <- sqrt(var(result$coef_mixed_sim_slope))
se_ave_mixed_sim_slope_REML <- mean(result$se_mixed_sim_slope_REML)
se_ave_mixed_sim_slope_DL <- mean(result$se_mixed_sim_slope_DL)
se_ave_mixed_sim_slope_AD <- mean(result$se_mixed_sim_slope_AD)

sd_mixed_sim_cov_slope <- sqrt(var(result$coef_mixed_sim_cov_slope))
se_ave_mixed_sim_cov_slope_REML <- mean(result$se_mixed_sim_cov_slope_REML)
se_ave_mixed_sim_cov_slope_DL <- mean(result$se_mixed_sim_cov_slope_DL)
se_ave_mixed_sim_cov_slope_AD <- mean(result$se_mixed_sim_cov_slope_AD)

############################################################################################################
#Function to calculate coverage probability 
true_parameter_in_ci<-function(result,point_estimate,t,se,true){
  true_in_ci<-sapply(1:nrep,function(i){
    lower_ci<-result[i,point_estimate]-1.96*result[i,se]
    upper_ci<-result[i,point_estimate]+1.96*result[i,se]
    if(true>=lower_ci & true<=upper_ci){1}else{0}
  })
  cov<-100*sum(true_in_ci)/nrep
  
  true_in_ci_ap<-sapply(1:nrep,function(i){
    lower_ci_ap<-result[i,point_estimate]-result[i,t]*result[i,se]
    upper_ci_ap<-result[i,point_estimate]+result[i,t]*result[i,se]
    if(true>=lower_ci_ap & true<=upper_ci_ap){1}else{0}
  })
  cov_ap<-100*sum(true_in_ci_ap)/nrep
  return(list("cov"=cov,"cov_ap"=cov_ap))
}

############################################################################################################
#I: mean outcome under treatment

#naive
cov_naive_1_est<-true_parameter_in_ci(result,"coef_naive_1","t_naive","se_naive_1",true=theta)
cov_naive_1<-cov_naive_1_est[[1]];cov_naive_1_ap<-cov_naive_1_est[[2]]

#naive_cov
cov_naive_1_cov_est<-true_parameter_in_ci(result,"coef_naive_1_cov","t_naive_cov","se_naive_1_cov",true=theta)
cov_naive_1_cov<-cov_naive_1_cov_est[[1]];cov_naive_1_cov_ap<-cov_naive_1_cov_est[[2]]

#fixed
cov_fixed_1_REML_est<-true_parameter_in_ci(result,"coef_fixed_1","t_fixed_1_REML","se_fixed_1_REML",true=theta)
cov_fixed_1_REML<-cov_fixed_1_REML_est[[1]];cov_fixed_1_REML_ap<-cov_fixed_1_REML_est[[2]]

cov_fixed_1_DL_est<-true_parameter_in_ci(result,"coef_fixed_1","t_fixed_1_DL","se_fixed_1_DL",true=theta)
cov_fixed_1_DL<-cov_fixed_1_DL_est[[1]];cov_fixed_1_DL_ap<-cov_fixed_1_DL_est[[2]]

cov_fixed_1_AD_est<-true_parameter_in_ci(result,"coef_fixed_1","t_fixed_1_AD","se_fixed_1_AD",true=theta)
cov_fixed_1_AD<-cov_fixed_1_AD_est[[1]];cov_fixed_1_AD_ap<-cov_fixed_1_AD_est[[2]]


#fixed_cov
cov_fixed_cov_1_REML_est<-true_parameter_in_ci(result,"coef_fixed_1_cov","t_fixed_1_cov_REML","se_fixed_1_cov_REML",true=theta)
cov_fixed_cov_1_REML<-cov_fixed_cov_1_REML_est[[1]];cov_fixed_cov_1_REML_ap<-cov_fixed_cov_1_REML_est[[2]]

cov_fixed_cov_1_DL_est<-true_parameter_in_ci(result,"coef_fixed_1_cov","t_fixed_1_cov_DL","se_fixed_1_cov_DL",true=theta)
cov_fixed_cov_1_DL<-cov_fixed_cov_1_DL_est[[1]];cov_fixed_cov_1_DL_ap<-cov_fixed_cov_1_DL_est[[2]]

cov_fixed_cov_1_AD_est<-true_parameter_in_ci(result,"coef_fixed_1_cov","t_fixed_1_cov_AD","se_fixed_1_cov_AD",true=theta)
cov_fixed_cov_1_AD<-cov_fixed_cov_1_AD_est[[1]];cov_fixed_cov_1_AD_ap<-cov_fixed_cov_1_AD_est[[2]]


#mixed
cov_mixed_1_REML_est<-true_parameter_in_ci(result,"coef_mixed_1","t_mixed_1_REML","se_mixed_1_REML",true=theta)
cov_mixed_1_REML<-cov_mixed_1_REML_est[[1]];cov_mixed_1_REML_ap<-cov_mixed_1_REML_est[[2]]

cov_mixed_1_DL_est<-true_parameter_in_ci(result,"coef_mixed_1","t_mixed_1_DL","se_mixed_1_DL",true=theta)
cov_mixed_1_DL<-cov_mixed_1_DL_est[[1]];cov_mixed_1_DL_ap<-cov_mixed_1_DL_est[[2]]

cov_mixed_1_AD_est<-true_parameter_in_ci(result,"coef_mixed_1","t_mixed_1_AD","se_mixed_1_AD",true=theta)
cov_mixed_1_AD<-cov_mixed_1_AD_est[[1]];cov_mixed_1_AD_ap<-cov_mixed_1_AD_est[[2]]


#mixed_cov
cov_mixed_cov_1_REML_est<-true_parameter_in_ci(result,"coef_mixed_1_cov","t_mixed_1_cov_REML","se_mixed_1_cov_REML",true=theta)
cov_mixed_cov_1_REML<-cov_mixed_cov_1_REML_est[[1]];cov_mixed_cov_1_REML_ap<-cov_mixed_cov_1_REML_est[[2]]

cov_mixed_cov_1_DL_est<-true_parameter_in_ci(result,"coef_mixed_1_cov","t_mixed_1_cov_DL","se_mixed_1_cov_DL",true=theta)
cov_mixed_cov_1_DL<-cov_mixed_cov_1_DL_est[[1]];cov_mixed_cov_1_DL_ap<-cov_mixed_cov_1_DL_est[[2]]

cov_mixed_cov_1_AD_est<-true_parameter_in_ci(result,"coef_mixed_1_cov","t_mixed_1_cov_AD","se_mixed_1_cov_AD",true=theta)
cov_mixed_cov_1_AD<-cov_mixed_cov_1_AD_est[[1]];cov_mixed_cov_1_AD_ap<-cov_mixed_cov_1_AD_est[[2]]


#mixed_slope
cov_mixed_slope_1_REML_est<-true_parameter_in_ci(result,"coef_mixed_1_slope","t_mixed_1_slope_REML","se_mixed_1_slope_REML",true=theta)
cov_mixed_slope_1_REML<-cov_mixed_slope_1_REML_est[[1]];cov_mixed_slope_1_REML_ap<-cov_mixed_slope_1_REML_est[[2]]

cov_mixed_slope_1_DL_est<-true_parameter_in_ci(result,"coef_mixed_1_slope","t_mixed_1_slope_DL","se_mixed_1_slope_DL",true=theta)
cov_mixed_slope_1_DL<-cov_mixed_slope_1_DL_est[[1]];cov_mixed_slope_1_DL_ap<-cov_mixed_slope_1_DL_est[[2]]

cov_mixed_slope_1_AD_est<-true_parameter_in_ci(result,"coef_mixed_1_slope","t_mixed_1_slope_AD","se_mixed_1_slope_AD",true=theta)
cov_mixed_slope_1_AD<-cov_mixed_slope_1_AD_est[[1]];cov_mixed_slope_1_AD_ap<-cov_mixed_slope_1_AD_est[[2]]


#mixed_cov_slope
cov_mixed_cov_slope_1_REML_est<-true_parameter_in_ci(result,"coef_mixed_1_cov_slope","t_mixed_1_cov_slope_REML","se_mixed_1_cov_slope_REML",true=theta)
cov_mixed_cov_slope_1_REML<-cov_mixed_cov_slope_1_REML_est[[1]];cov_mixed_cov_slope_1_REML_ap<-cov_mixed_cov_slope_1_REML_est[[2]]

cov_mixed_cov_slope_1_DL_est<-true_parameter_in_ci(result,"coef_mixed_1_cov_slope","t_mixed_1_cov_slope_DL","se_mixed_1_cov_slope_DL",true=theta)
cov_mixed_cov_slope_1_DL<-cov_mixed_cov_slope_1_DL_est[[1]];cov_mixed_cov_slope_1_DL_ap<-cov_mixed_cov_slope_1_DL_est[[2]]

cov_mixed_cov_slope_1_AD_est<-true_parameter_in_ci(result,"coef_mixed_1_cov_slope","t_mixed_1_cov_slope_AD","se_mixed_1_cov_slope_AD",true=theta)
cov_mixed_cov_slope_1_AD<-cov_mixed_cov_slope_1_AD_est[[1]];cov_mixed_cov_slope_1_AD_ap<-cov_mixed_cov_slope_1_AD_est[[2]]


#mixed_sim
cov_mixed_sim_1_REML_est<-true_parameter_in_ci(result,"coef_mixed_sim_1","t_mixed_sim_1_REML","se_mixed_sim_1_REML",true=theta)
cov_mixed_sim_1_REML<-cov_mixed_sim_1_REML_est[[1]];cov_mixed_sim_1_REML_ap<-cov_mixed_sim_1_REML_est[[2]]

cov_mixed_sim_1_DL_est<-true_parameter_in_ci(result,"coef_mixed_sim_1","t_mixed_sim_1_DL","se_mixed_sim_1_DL",true=theta)
cov_mixed_sim_1_DL<-cov_mixed_sim_1_DL_est[[1]];cov_mixed_sim_1_DL_ap<-cov_mixed_sim_1_DL_est[[2]]

cov_mixed_sim_1_AD_est<-true_parameter_in_ci(result,"coef_mixed_sim_1","t_mixed_sim_1_AD","se_mixed_sim_1_AD",true=theta)
cov_mixed_sim_1_AD<-cov_mixed_sim_1_AD_est[[1]];cov_mixed_sim_1_AD_ap<-cov_mixed_sim_1_AD_est[[2]]


#mixed_sim_cov
cov_mixed_sim_cov_1_REML_est<-true_parameter_in_ci(result,"coef_mixed_sim_1_cov","t_mixed_sim_1_cov_REML","se_mixed_sim_1_cov_REML",true=theta)
cov_mixed_sim_cov_1_REML<-cov_mixed_sim_cov_1_REML_est[[1]];cov_mixed_sim_cov_1_REML_ap<-cov_mixed_sim_cov_1_REML_est[[2]]

cov_mixed_sim_cov_1_DL_est<-true_parameter_in_ci(result,"coef_mixed_sim_1_cov","t_mixed_sim_1_cov_DL","se_mixed_sim_1_cov_DL",true=theta)
cov_mixed_sim_cov_1_DL<-cov_mixed_sim_cov_1_DL_est[[1]];cov_mixed_sim_cov_1_DL_ap<-cov_mixed_sim_cov_1_DL_est[[2]]

cov_mixed_sim_cov_1_AD_est<-true_parameter_in_ci(result,"coef_mixed_sim_1_cov","t_mixed_sim_1_cov_AD","se_mixed_sim_1_cov_AD",true=theta)
cov_mixed_sim_cov_1_AD<-cov_mixed_sim_cov_1_AD_est[[1]];cov_mixed_sim_cov_1_AD_ap<-cov_mixed_sim_cov_1_AD_est[[2]]


#mixed_sim_slope
cov_mixed_sim_slope_1_REML_est<-true_parameter_in_ci(result,"coef_mixed_sim_1_slope","t_mixed_sim_1_slope_REML","se_mixed_sim_1_slope_REML",true=theta)
cov_mixed_sim_slope_1_REML<-cov_mixed_sim_slope_1_REML_est[[1]];cov_mixed_sim_slope_1_REML_ap<-cov_mixed_sim_slope_1_REML_est[[2]]

cov_mixed_sim_slope_1_DL_est<-true_parameter_in_ci(result,"coef_mixed_sim_1_slope","t_mixed_sim_1_slope_DL","se_mixed_sim_1_slope_DL",true=theta)
cov_mixed_sim_slope_1_DL<-cov_mixed_sim_slope_1_DL_est[[1]];cov_mixed_sim_slope_1_DL_ap<-cov_mixed_sim_slope_1_DL_est[[2]]

cov_mixed_sim_slope_1_AD_est<-true_parameter_in_ci(result,"coef_mixed_sim_1_slope","t_mixed_sim_1_slope_AD","se_mixed_sim_1_slope_AD",true=theta)
cov_mixed_sim_slope_1_AD<-cov_mixed_sim_slope_1_AD_est[[1]];cov_mixed_sim_slope_1_AD_ap<-cov_mixed_sim_slope_1_AD_est[[2]]


#mixed_sim_cov_slope
cov_mixed_sim_cov_slope_1_REML_est<-true_parameter_in_ci(result,"coef_mixed_sim_1_cov_slope","t_mixed_sim_1_cov_slope_REML","se_mixed_sim_1_cov_slope_REML",true=theta)
cov_mixed_sim_cov_slope_1_REML<-cov_mixed_sim_cov_slope_1_REML_est[[1]];cov_mixed_sim_cov_slope_1_REML_ap<-cov_mixed_sim_cov_slope_1_REML_est[[2]]

cov_mixed_sim_cov_slope_1_DL_est<-true_parameter_in_ci(result,"coef_mixed_sim_1_cov_slope","t_mixed_sim_1_cov_slope_DL","se_mixed_sim_1_cov_slope_DL",true=theta)
cov_mixed_sim_cov_slope_1_DL<-cov_mixed_sim_cov_slope_1_DL_est[[1]];cov_mixed_sim_cov_slope_1_DL_ap<-cov_mixed_sim_cov_slope_1_DL_est[[2]]

cov_mixed_sim_cov_slope_1_AD_est<-true_parameter_in_ci(result,"coef_mixed_sim_1_cov_slope","t_mixed_sim_1_cov_slope_AD","se_mixed_sim_1_cov_slope_AD",true=theta)
cov_mixed_sim_cov_slope_1_AD<-cov_mixed_sim_cov_slope_1_AD_est[[1]];cov_mixed_sim_cov_slope_1_AD_ap<-cov_mixed_sim_cov_slope_1_AD_est[[2]]


############################################################################################################
#II:treatment effect

#naive
cov_naive_est<-true_parameter_in_ci(result,"coef_naive","t_naive","se_naive",true=beta)
cov_naive<-cov_naive_est[[1]];cov_naive_ap<-cov_naive_est[[2]]

#naive_cov
cov_naive_cov_est<-true_parameter_in_ci(result,"coef_naive_cov","t_naive_cov","se_naive_cov",true=beta)
cov_naive_cov<-cov_naive_cov_est[[1]];cov_naive_cov_ap<-cov_naive_cov_est[[2]]

#fixed
cov_fixed_REML_est<-true_parameter_in_ci(result,"coef_fixed","t_fixed_REML","se_fixed_REML",true=beta)
cov_fixed_REML<-cov_fixed_REML_est[[1]];cov_fixed_REML_ap<-cov_fixed_REML_est[[2]]

cov_fixed_DL_est<-true_parameter_in_ci(result,"coef_fixed","t_fixed_DL","se_fixed_DL",true=beta)
cov_fixed_DL<-cov_fixed_DL_est[[1]];cov_fixed_DL_ap<-cov_fixed_DL_est[[2]]

cov_fixed_AD_est<-true_parameter_in_ci(result,"coef_fixed","t_fixed_AD","se_fixed_AD",true=beta)
cov_fixed_AD<-cov_fixed_AD_est[[1]];cov_fixed_AD_ap<-cov_fixed_AD_est[[2]]


#fixed_cov
cov_fixed_cov_REML_est<-true_parameter_in_ci(result,"coef_fixed_cov","t_fixed_cov_REML","se_fixed_cov_REML",true=beta)
cov_fixed_cov_REML<-cov_fixed_cov_REML_est[[1]];cov_fixed_cov_REML_ap<-cov_fixed_cov_REML_est[[2]]

cov_fixed_cov_DL_est<-true_parameter_in_ci(result,"coef_fixed_cov","t_fixed_cov_DL","se_fixed_cov_DL",true=beta)
cov_fixed_cov_DL<-cov_fixed_cov_DL_est[[1]];cov_fixed_cov_DL_ap<-cov_fixed_cov_DL_est[[2]]

cov_fixed_cov_AD_est<-true_parameter_in_ci(result,"coef_fixed_cov","t_fixed_cov_AD","se_fixed_cov_AD",true=beta)
cov_fixed_cov_AD<-cov_fixed_cov_AD_est[[1]];cov_fixed_cov_AD_ap<-cov_fixed_cov_AD_est[[2]]


#mixed
cov_mixed_REML_est<-true_parameter_in_ci(result,"coef_mixed","t_mixed_REML","se_mixed_REML",true=beta)
cov_mixed_REML<-cov_mixed_REML_est[[1]];cov_mixed_REML_ap<-cov_mixed_REML_est[[2]]

cov_mixed_DL_est<-true_parameter_in_ci(result,"coef_mixed","t_mixed_DL","se_mixed_DL",true=beta)
cov_mixed_DL<-cov_mixed_DL_est[[1]];cov_mixed_DL_ap<-cov_mixed_DL_est[[2]]

cov_mixed_AD_est<-true_parameter_in_ci(result,"coef_mixed","t_mixed_AD","se_mixed_AD",true=beta)
cov_mixed_AD<-cov_mixed_AD_est[[1]];cov_mixed_AD_ap<-cov_mixed_AD_est[[2]]


#mixed_cov
cov_mixed_cov_REML_est<-true_parameter_in_ci(result,"coef_mixed_cov","t_mixed_cov_REML","se_mixed_cov_REML",true=beta)
cov_mixed_cov_REML<-cov_mixed_cov_REML_est[[1]];cov_mixed_cov_REML_ap<-cov_mixed_cov_REML_est[[2]]

cov_mixed_cov_DL_est<-true_parameter_in_ci(result,"coef_mixed_cov","t_mixed_cov_DL","se_mixed_cov_DL",true=beta)
cov_mixed_cov_DL<-cov_mixed_cov_DL_est[[1]];cov_mixed_cov_DL_ap<-cov_mixed_cov_DL_est[[2]]

cov_mixed_cov_AD_est<-true_parameter_in_ci(result,"coef_mixed_cov","t_mixed_cov_AD","se_mixed_cov_AD",true=beta)
cov_mixed_cov_AD<-cov_mixed_cov_AD_est[[1]];cov_mixed_cov_AD_ap<-cov_mixed_cov_AD_est[[2]]


#mixed_slope
cov_mixed_slope_REML_est<-true_parameter_in_ci(result,"coef_mixed_slope","t_mixed_slope_REML","se_mixed_slope_REML",true=beta)
cov_mixed_slope_REML<-cov_mixed_slope_REML_est[[1]];cov_mixed_slope_REML_ap<-cov_mixed_slope_REML_est[[2]]

cov_mixed_slope_DL_est<-true_parameter_in_ci(result,"coef_mixed_slope","t_mixed_slope_DL","se_mixed_slope_DL",true=beta)
cov_mixed_slope_DL<-cov_mixed_slope_DL_est[[1]];cov_mixed_slope_DL_ap<-cov_mixed_slope_DL_est[[2]]

cov_mixed_slope_AD_est<-true_parameter_in_ci(result,"coef_mixed_slope","t_mixed_slope_AD","se_mixed_slope_AD",true=beta)
cov_mixed_slope_AD<-cov_mixed_slope_AD_est[[1]];cov_mixed_slope_AD_ap<-cov_mixed_slope_AD_est[[2]]


#mixed_cov_slope
cov_mixed_cov_slope_REML_est<-true_parameter_in_ci(result,"coef_mixed_cov_slope","t_mixed_cov_slope_REML","se_mixed_cov_slope_REML",true=beta)
cov_mixed_cov_slope_REML<-cov_mixed_cov_slope_REML_est[[1]];cov_mixed_cov_slope_REML_ap<-cov_mixed_cov_slope_REML_est[[2]]

cov_mixed_cov_slope_DL_est<-true_parameter_in_ci(result,"coef_mixed_cov_slope","t_mixed_cov_slope_DL","se_mixed_cov_slope_DL",true=beta)
cov_mixed_cov_slope_DL<-cov_mixed_cov_slope_DL_est[[1]];cov_mixed_cov_slope_DL_ap<-cov_mixed_cov_slope_DL_est[[2]]

cov_mixed_cov_slope_AD_est<-true_parameter_in_ci(result,"coef_mixed_cov_slope","t_mixed_cov_slope_AD","se_mixed_cov_slope_AD",true=beta)
cov_mixed_cov_slope_AD<-cov_mixed_cov_slope_AD_est[[1]];cov_mixed_cov_slope_AD_ap<-cov_mixed_cov_slope_AD_est[[2]]


#mixed_sim
cov_mixed_sim_REML_est<-true_parameter_in_ci(result,"coef_mixed_sim","t_mixed_sim_REML","se_mixed_sim_REML",true=beta)
cov_mixed_sim_REML<-cov_mixed_sim_REML_est[[1]];cov_mixed_sim_REML_ap<-cov_mixed_sim_REML_est[[2]]

cov_mixed_sim_DL_est<-true_parameter_in_ci(result,"coef_mixed_sim","t_mixed_sim_DL","se_mixed_sim_DL",true=beta)
cov_mixed_sim_DL<-cov_mixed_sim_DL_est[[1]];cov_mixed_sim_DL_ap<-cov_mixed_sim_DL_est[[2]]

cov_mixed_sim_AD_est<-true_parameter_in_ci(result,"coef_mixed_sim","t_mixed_sim_AD","se_mixed_sim_AD",true=beta)
cov_mixed_sim_AD<-cov_mixed_sim_AD_est[[1]];cov_mixed_sim_AD_ap<-cov_mixed_sim_AD_est[[2]]


#mixed_sim_cov
cov_mixed_sim_cov_REML_est<-true_parameter_in_ci(result,"coef_mixed_sim_cov","t_mixed_sim_cov_REML","se_mixed_sim_cov_REML",true=beta)
cov_mixed_sim_cov_REML<-cov_mixed_sim_cov_REML_est[[1]];cov_mixed_sim_cov_REML_ap<-cov_mixed_sim_cov_REML_est[[2]]

cov_mixed_sim_cov_DL_est<-true_parameter_in_ci(result,"coef_mixed_sim_cov","t_mixed_sim_cov_DL","se_mixed_sim_cov_DL",true=beta)
cov_mixed_sim_cov_DL<-cov_mixed_sim_cov_DL_est[[1]];cov_mixed_sim_cov_DL_ap<-cov_mixed_sim_cov_DL_est[[2]]

cov_mixed_sim_cov_AD_est<-true_parameter_in_ci(result,"coef_mixed_sim_cov","t_mixed_sim_cov_AD","se_mixed_sim_cov_AD",true=beta)
cov_mixed_sim_cov_AD<-cov_mixed_sim_cov_AD_est[[1]];cov_mixed_sim_cov_AD_ap<-cov_mixed_sim_cov_AD_est[[2]]


#mixed_sim_slope
cov_mixed_sim_slope_REML_est<-true_parameter_in_ci(result,"coef_mixed_sim_slope","t_mixed_sim_slope_REML","se_mixed_sim_slope_REML",true=beta)
cov_mixed_sim_slope_REML<-cov_mixed_sim_slope_REML_est[[1]];cov_mixed_sim_slope_REML_ap<-cov_mixed_sim_slope_REML_est[[2]]

cov_mixed_sim_slope_DL_est<-true_parameter_in_ci(result,"coef_mixed_sim_slope","t_mixed_sim_slope_DL","se_mixed_sim_slope_DL",true=beta)
cov_mixed_sim_slope_DL<-cov_mixed_sim_slope_DL_est[[1]];cov_mixed_sim_slope_DL_ap<-cov_mixed_sim_slope_DL_est[[2]]

cov_mixed_sim_slope_AD_est<-true_parameter_in_ci(result,"coef_mixed_sim_slope","t_mixed_sim_slope_AD","se_mixed_sim_slope_AD",true=beta)
cov_mixed_sim_slope_AD<-cov_mixed_sim_slope_AD_est[[1]];cov_mixed_sim_slope_AD_ap<-cov_mixed_sim_slope_AD_est[[2]]


#mixed_sim_cov_slope
cov_mixed_sim_cov_slope_REML_est<-true_parameter_in_ci(result,"coef_mixed_sim_cov_slope","t_mixed_sim_cov_slope_REML","se_mixed_sim_cov_slope_REML",true=beta)
cov_mixed_sim_cov_slope_REML<-cov_mixed_sim_cov_slope_REML_est[[1]];cov_mixed_sim_cov_slope_REML_ap<-cov_mixed_sim_cov_slope_REML_est[[2]]

cov_mixed_sim_cov_slope_DL_est<-true_parameter_in_ci(result,"coef_mixed_sim_cov_slope","t_mixed_sim_cov_slope_DL","se_mixed_sim_cov_slope_DL",true=beta)
cov_mixed_sim_cov_slope_DL<-cov_mixed_sim_cov_slope_DL_est[[1]];cov_mixed_sim_cov_slope_DL_ap<-cov_mixed_sim_cov_slope_DL_est[[2]]

cov_mixed_sim_cov_slope_AD_est<-true_parameter_in_ci(result,"coef_mixed_sim_cov_slope","t_mixed_sim_cov_slope_AD","se_mixed_sim_cov_slope_AD",true=beta)
cov_mixed_sim_cov_slope_AD<-cov_mixed_sim_cov_slope_AD_est[[1]];cov_mixed_sim_cov_slope_AD_ap<-cov_mixed_sim_cov_slope_AD_est[[2]]


############################################################################################################
#Export result to latex
# Create a data frame with your data

df_1 <- data.frame(  
  Method=c("Naive","Naive cov","Fixed","Fixed cov",
           "Mixed(1|c) BLUP","Mixed(1|c) cov BLUP",
           "Mixed(1+A|c) BLUP","Mixed(1+A|c) cov BLUP",
           "Mixed(1|c) Sam.","Mixed(1|c) cov Sam.",
           "Mixed(1+A|c) Sam.","Mixed(1+A|c) cov Sam."),
  
  SD_CM = c(sd_naive_1,sd_naive_1_cov,sd_fixed_1,sd_fixed_1_cov,
            sd_mixed_1,sd_mixed_1_cov,sd_mixed_1_slope,sd_mixed_1_cov_slope,
            sd_mixed_sim_1,sd_mixed_sim_1_cov,sd_mixed_sim_1_slope,sd_mixed_sim_1_cov_slope),
  
  Se_REML_CM = c(se_ave_naive_1,se_ave_naive_1_cov,se_ave_fixed_1_REML,se_ave_fixed_1_cov_REML,
                 se_ave_mixed_1_REML,se_ave_mixed_1_cov_REML,se_ave_mixed_1_slope_REML,se_ave_mixed_1_cov_slope_REML,
                 se_ave_mixed_sim_1_REML,se_ave_mixed_sim_1_cov_REML,se_ave_mixed_sim_1_slope_REML,se_ave_mixed_sim_1_cov_slope_REML),
  
  Se_DL_CM = c(se_ave_naive_1,se_ave_naive_1_cov,se_ave_fixed_1_DL,se_ave_fixed_1_cov_DL,
               se_ave_mixed_1_DL,se_ave_mixed_1_cov_DL,se_ave_mixed_1_slope_DL,se_ave_mixed_1_cov_slope_DL,
               se_ave_mixed_sim_1_DL,se_ave_mixed_sim_1_cov_DL,se_ave_mixed_sim_1_slope_DL,se_ave_mixed_sim_1_cov_slope_DL),
  
  Se_AD_CM = c(se_ave_naive_1,se_ave_naive_1_cov,se_ave_fixed_1_AD,se_ave_fixed_1_cov_AD,
               se_ave_mixed_1_AD,se_ave_mixed_1_cov_AD,se_ave_mixed_1_slope_AD,se_ave_mixed_1_cov_slope_AD,
               se_ave_mixed_sim_1_AD,se_ave_mixed_sim_1_cov_AD,se_ave_mixed_sim_1_slope_AD,se_ave_mixed_sim_1_cov_slope_AD),
  
  Cov_REML_CM = c(cov_naive_1_ap,cov_naive_1_cov_ap,cov_fixed_1_REML_ap,cov_fixed_cov_1_REML_ap,
                  cov_mixed_1_REML_ap,cov_mixed_cov_1_REML_ap,cov_mixed_slope_1_REML_ap,cov_mixed_cov_slope_1_REML_ap,
                  cov_mixed_sim_1_REML_ap,cov_mixed_sim_cov_1_REML_ap,cov_mixed_sim_slope_1_REML_ap,cov_mixed_sim_cov_slope_1_REML_ap),
  
  Cov_DL_CM = c(cov_naive_1_ap,cov_naive_1_cov_ap,cov_fixed_1_DL_ap,cov_fixed_cov_1_DL_ap,
                cov_mixed_1_DL_ap,cov_mixed_cov_1_DL_ap,cov_mixed_slope_1_DL_ap,cov_mixed_cov_slope_1_DL_ap,
                cov_mixed_sim_1_DL_ap,cov_mixed_sim_cov_1_DL_ap,cov_mixed_sim_slope_1_DL_ap,cov_mixed_sim_cov_slope_1_DL_ap),
  
  Cov_AD_CM = c(cov_naive_1_ap,cov_naive_1_cov_ap,cov_fixed_1_AD_ap,cov_fixed_cov_1_AD_ap,
                cov_mixed_1_AD_ap,cov_mixed_cov_1_AD_ap,cov_mixed_slope_1_AD_ap,cov_mixed_cov_slope_1_AD_ap,
                cov_mixed_sim_1_AD_ap,cov_mixed_sim_cov_1_AD_ap,cov_mixed_sim_slope_1_AD_ap,cov_mixed_sim_cov_slope_1_AD_ap),
  
  SD_ATE = c(sd_naive,sd_naive_cov,sd_fixed,sd_fixed_cov,
             sd_mixed,sd_mixed_cov,sd_mixed_slope,sd_mixed_cov_slope,
             sd_mixed_sim,sd_mixed_sim_cov,sd_mixed_sim_slope,sd_mixed_sim_cov_slope),
  
  Se_REML_ATE = c(se_ave_naive,se_ave_naive_cov,se_ave_fixed_REML,se_ave_fixed_cov_REML,
                  se_ave_mixed_REML,se_ave_mixed_cov_REML,se_ave_mixed_slope_REML,se_ave_mixed_cov_slope_REML,
                  se_ave_mixed_sim_REML,se_ave_mixed_sim_cov_REML,se_ave_mixed_sim_slope_REML,se_ave_mixed_sim_cov_slope_REML),
  
  Se_DL_ATE = c(se_ave_naive,se_ave_naive_cov,se_ave_fixed_DL,se_ave_fixed_cov_DL,
                se_ave_mixed_DL,se_ave_mixed_cov_DL,se_ave_mixed_slope_DL,se_ave_mixed_cov_slope_DL,
                se_ave_mixed_sim_DL,se_ave_mixed_sim_cov_DL,se_ave_mixed_sim_slope_DL,se_ave_mixed_sim_cov_slope_DL),
  
  Se_AD_ATE = c(se_ave_naive,se_ave_naive_cov,se_ave_fixed_AD,se_ave_fixed_cov_AD,
                se_ave_mixed_AD,se_ave_mixed_cov_AD,se_ave_mixed_slope_AD,se_ave_mixed_cov_slope_AD,
                se_ave_mixed_sim_AD,se_ave_mixed_sim_cov_AD,se_ave_mixed_sim_slope_AD,se_ave_mixed_sim_cov_slope_AD),
  
  Cov_REML_ATE = c(cov_naive_ap,cov_naive_cov_ap,cov_fixed_REML_ap,cov_fixed_cov_REML_ap,
                   cov_mixed_REML_ap,cov_mixed_cov_REML_ap,cov_mixed_slope_REML_ap,cov_mixed_cov_slope_REML_ap,
                   cov_mixed_sim_REML_ap,cov_mixed_sim_cov_REML_ap,cov_mixed_sim_slope_REML_ap,cov_mixed_sim_cov_slope_REML_ap),
  
  Cov_DL_ATE = c(cov_naive_ap,cov_naive_cov_ap,cov_fixed_DL_ap,cov_fixed_cov_DL_ap,
                 cov_mixed_DL_ap,cov_mixed_cov_DL_ap,cov_mixed_slope_DL_ap,cov_mixed_cov_slope_DL_ap,
                 cov_mixed_sim_DL_ap,cov_mixed_sim_cov_DL_ap,cov_mixed_sim_slope_DL_ap,cov_mixed_sim_cov_slope_DL_ap),
  
  Cov_AD_ATE = c(cov_naive_ap,cov_naive_cov_ap,cov_fixed_AD_ap,cov_fixed_cov_AD_ap,
                 cov_mixed_AD_ap,cov_mixed_cov_AD_ap,cov_mixed_slope_AD_ap,cov_mixed_cov_slope_AD_ap,
                 cov_mixed_sim_AD_ap,cov_mixed_sim_cov_AD_ap,cov_mixed_sim_slope_AD_ap,cov_mixed_sim_cov_slope_AD_ap)
)

# Convert the data frame to LaTeX format
latex_table_1 <- xtable(df_1,digits = 3)

# Print the LaTeX table
print(latex_table_1, include.rownames = FALSE)

###>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

#Bias and MSE for CM
df_CM <- data.frame(  
  Method=c("Bias","MSE"),
  Naive = c(bias_mean_coef_naive_1,mse_naive_1),
  Naive_cov = c(bias_mean_coef_naive_1_cov,mse_naive_1_cov),
  Fixed = c(bias_mean_coef_fixed_1,mse_fixed_1),
  Fixed_cov = c(bias_mean_coef_fixed_1_cov,mse_fixed_1_cov),
  Mixed = c(bias_mean_coef_mixed_1,mse_mixed_1),
  Mixed_cov = c(bias_mean_coef_mixed_1_cov,mse_mixed_1_cov),
  Mixed_slope = c(bias_mean_coef_mixed_1_slope,mse_mixed_1_slope),
  Mixed_cov_slope = c(bias_mean_coef_mixed_1_cov_slope,mse_mixed_1_cov_slope),
  Mixed_sim = c(bias_mean_coef_mixed_sim_1,mse_mixed_sim_1),
  Mixed_sim_cov = c(bias_mean_coef_mixed_sim_1_cov,mse_mixed_sim_1_cov),
  Mixed_sim_slope = c(bias_mean_coef_mixed_sim_1_slope,mse_mixed_sim_1_slope),
  Mixed_sim_cov_slope = c(bias_mean_coef_mixed_sim_1_cov_slope,mse_mixed_sim_1_cov_slope))

# Convert the data frame to LaTeX format
latex_table_CM <- xtable(df_CM,digits=4)

# Print the LaTeX table
print(latex_table_CM,include.rownames = FALSE)

#Bias and MSE for ATE
df <- data.frame(  
  Method=c("Bias","MSE"),
  Naive = c(bias_mean_coef_naive,mse_naive),
  Naive_cov = c(bias_mean_coef_naive_cov,mse_naive_cov),
  Fixed = c(bias_mean_coef_fixed,mse_fixed),
  Fixed_cov = c(bias_mean_coef_fixed_cov,mse_fixed_cov),
  Mixed = c(bias_mean_coef_mixed,mse_mixed),
  Mixed_cov = c(bias_mean_coef_mixed_cov,mse_mixed_cov),
  Mixed_slope = c(bias_mean_coef_mixed_slope,mse_mixed_slope),
  Mixed_cov_slope = c(bias_mean_coef_mixed_cov_slope,mse_mixed_cov_slope),
  Mixed_sim = c(bias_mean_coef_mixed_sim,mse_mixed_sim),
  Mixed_sim_cov = c(bias_mean_coef_mixed_sim_cov,mse_mixed_sim_cov),
  Mixed_sim_slope = c(bias_mean_coef_mixed_sim_slope,mse_mixed_sim_slope),
  Mixed_sim_cov_slope = c(bias_mean_coef_mixed_sim_cov_slope,mse_mixed_sim_cov_slope))

# Convert the data frame to LaTeX format
latex_table <- xtable(df,digits=4)

# Print the LaTeX table
print(latex_table,include.rownames = FALSE)

#********************end*****************************************************
