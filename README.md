---
title: "Accounting for Clustering in Multi-Center Trials"
output: html_document
---

## Data generating mechanism

```{r}
# Required packages
library(lme4)
library(metafor)
library(LaplacesDemon)

# Number of centers
k <- 100

# Center sizes
n_c <- c(
  1, 3, 5, 2, 4, 3, 3, 4, 7, 5, 4, 7, 1, 4, 5, 8, 4, 9, 1, 8,
  7, 6, 24, 1, 3, 7, 5, 6, 1, 5, 2, 7, 8, 1, 6, 7, 4, 8, 4, 10,
  6, 7, 4, 3, 2, 7, 1, 2, 3, 2, 2, 1, 3, 5, 2, 4, 4, 3, 4, 7,
  5, 4, 7, 1, 4, 5, 8, 4, 9, 3, 8, 7, 4, 9, 3, 7, 5, 6, 9, 5,
  2, 7, 8, 9, 6, 7, 4, 8, 4, 10, 6, 7, 4, 3, 2, 6, 3, 2, 3, 4
)

# Total sample size
n <- sum(n_c)

# Random-effects variances
sigma_sequare_b0 <- 0.75
sigma_sequare_b1 <- 0.5
sigma_sequare_b2 <- 0.5

# Baseline covariates
X1 <- rbinom(n, 1, 0.3)
X2 <- rbinom(n, 1, 0.4)
X3 <- rnorm(n, 59, 13)
X4 <- rnorm(n, 47, 18)

# Treatment indicator
A <- rbinom(n, 1, 0.5)

# Random effects
b0 <- rnorm(k, 0, sqrt(sigma_sequare_b0))
b1 <- rnorm(k, 0, sqrt(sigma_sequare_b1))
b2 <- rnorm(k, 0, sqrt(sigma_sequare_b2))

# Center indicator
c <- rep(1:k, n_c)

# Outcome
Y <- rbinom(n,1,invlogit(3.22 +b0[c] +(0.28 + b1[c]) * A -(1.71 + b2[c]) * X1 -0.72 * X2 -0.04 * X3 -0.007 * X4))

# Data set
data <- data.frame(c, A, X1, X2, X3, X4, Y)
```

## Estimation
### Model fitting
Fit a mixed-effects logistic regression model including treatment and baseline covariates as fixed effects and allowing for center-specific random intercepts and random treatment slopes.

```{r}
Mixed_model <- glmer(Y ~ A + X1 + X2 + X3 + X4 + (1 + A | c), data = data, family = binomial(link = "logit"))
```

### Predicting
Using the fitted model, predict the fixed-effects component of the log-odds of the outcome for each patient under treatment, \(A = 1\).

```{r}
new_data <- data.frame(c,A = 1,X1,X2,X3,X4)
pred_fix <- predict(Mixed_model,newdata = new_data,type = "link",re.form = NA)
```

### Integration over the random-effects distribution
Estimate random effects based on their estimated distribution and average the resulting predicted outcomes across 1000 simulated draws.

```{r}
# Random-intercept variance
vc_df <- as.data.frame(VarCorr(Mixed_model))
intercept_var <- vc_df$vcov[1]

# Random-slope variance
slope_var_trt <- vc_df$vcov[vc_df$var1 == "A" & is.na(vc_df$var2)]

n <- length(A)
pred_sum <- numeric(n)
nsim <- 1000

for (i in 1:nsim) {
  # Simulate random intercepts and slopes from estimated variances
  est_u0 <- rnorm(length(unique(c)),0,sqrt(intercept_var))
  est_u1 <- rnorm(length(unique(c)),0,sqrt(slope_var_trt))
  pred <- plogis(pred_fix + est_u0[c] + est_u1[c])
  pred_sum <- pred_sum + pred
}
pred_ave <- pred_sum / nsim
```

### Estimation of randomization probabilities
```{r}
p_model <- glmer(A ~ X1 + X2 + X3 + X4 + (1 | c),data = data, family = binomial(link = "logit"))
new_dta <- data.frame(c,X1,X2,X3,X4)
p <- as.vector(predict(p_model,newdata = new_dta, type = "response"))
```

### Calculate influence functions
```{r}
IF <- A / p * (Y - pred_ave) + pred_ave
```

### Center-specific and overall estimation
```{r}
# Center-specific estimates
means <- as.vector(tapply(IF, c, mean))

# Overall estimate, weighting centers equally
est_CM <- mean(means)
```

## Inference
### Estimation of within-center variances

```{r}
data$IF <- IF
mixed <- lmer(IF ~ (1 | c), data = data)
res_var <- sigma(mixed)^2 / n_c
```

### Estimation of between-center variance
```{r}
# Using REML
model_REML <- rma(yi = means, vi = res_var, method = "REML", control = list(stepadj = 0.5, maxiter = 10000))
tau2_REML <- model_REML$tau2

# Using DL
model_DL <- rma(yi = means, vi = res_var, method = "DL")
tau2_DL <- model_DL$tau2

# Using DB
var_means <- mean((means - mean(means))^2)
sum_variances <- sum(res_var)
v <- var_means-((k - 1) / k^2) * sum_variances
tau2_DB <- max(0, v)
```

### Estimation of the standard error
For example, when using REML for the heterogeneity variance estimator:

```{r}
se_REML <- sqrt((tau2_REML + mean(res_var)) / k
)
```

### Construction of the confidence interval
```{r}
# Approximate the degrees of freedom using the REML estimate
# of the between-center variance
rho <- tau2_REML / (tau2_REML + mean(res_var))

df <- sum(n_c / (1 + (n_c - 1) * rho)) - 1

# Obtain the 95% t critical value
t_critical <- -qt(0.025, df)

# Construct the 95% confidence interval
CI_REML <- c(lower = est_CM - t_critical * se_REML, upper = est_CM + t_critical * se_REML)
CI_REML
```

## Citation
If you use this code, please cite:
> Alene M, Vansteelandt S, Van Lancker K. *Robust Covariate Adjustment in Multi-Center Randomized Trials.* arXiv preprint arXiv:2504.12760. 2025 Apr 17.
