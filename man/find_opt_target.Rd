\name{find_opt_target}
\alias{find_opt_target}
\title{Optimum mixture proportions and optimal order of addition of the components}
\usage{find_opt_target(m, model, target)}
\arguments{
\item{m}{number of mixture components}
\item{model}{a fitted model of class lm which fits a model for data from mixture order-of-addition experiment}
\item{target}{desired target value of response variable}
}
\value{returns optimum mixture proportions of the components and their optimal order-of-addition}
\description{
Find optimum mixture proportions and optimal order of addition of the components
}
\examples{
data(fish)
mixoofa.fit <- lm(y ~ -1 + (x1+x2+x3)^2 + z12+z13+z23, data = fish) 
summary(mixoofa.fit)
find_opt_target(m = 3, mixoofa.fit, target = 2.75)
}
